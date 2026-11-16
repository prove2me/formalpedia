-- Prove2me | Theorems.Thm_SeededShannon_Supplement_theorem_C_6
-- name    : SeededShannon.Supplement.theorem_C_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:49:09.534796+00:00
-- url     : https://prove2.me/theorems/71956f92-9c61-483f-9a58-575968f9e005
-- title:
--   Theorem C.6 — two-component Parvaresh–Vardy list recovery
-- statement:
--   Fix $0<\beta<1$, let $\lambda,\kappa,b\ge1$ be integers, and set $k=\lambda+1$. Let $q$ be a power of two satisfying
--   $$q\ge\max\Big\{\frac{8k}{\beta},\ \frac{256\,\kappa\, b\, k^2}{\beta^3}\Big\}.$$
--   There is an injective code $\mathrm{Encode}_{\mathrm{PV}}:\{0,1\}^\lambda\to(\mathbb F_q^2)^q$ with deterministic construction, encoding and list recovery in time $\mathrm{poly}(\lambda,q,b)$. Given lists $U_x\subseteq\mathbb F_q^2$, indexed by $x\in\mathbb F_q$, with
--   $$W:=\sum_{x\in\mathbb F_q}|U_x|\le\kappa\cdot b\cdot q^2,$$
--   recovery outputs exactly the messages whose codewords $c=\mathrm{Encode}_{\mathrm{PV}}(\mathbf x)$ satisfy
--   $$|\{x\in\mathbb F_q:c_x\in U_x\}|\ge\beta\cdot q.$$
--   The output list has size at most $\lceil 2\kappa bq/\beta\rceil$.
--
--   This code is the outer code of the sparse-partition embedding behind the partition obfuscator of Construction 6.1.
--
--   **Formalization Note** One encoding machine and one recovery machine, with a running-time exponent depending only on $\beta$, work for all admissible $(\lambda,q,\kappa,b)$ on input $(1^\lambda,1^q,1^\kappa,1^b,\cdot)$; computing the field data is part of these computations.
--
--   Differences from the source:
--   - encoding: 𝔽_q, 𝔽_q² and coordinates indexed by x ∈ 𝔽_q → the alphabet Fin q (pairs Fin q × Fin q) with binary symbol codes; coordinates indexed by Fin q; reason: the field structure does not enter the statement; any representation of 𝔽_q is in polynomial-time bijection with Fin q
--   - encoding: deterministic construction, encoding and list recovery in time poly(λ, q, b) → two fixed machines halting within (λ + q + b + 2)^c steps on (1^λ, 1^q, 1^κ, 1^b, input), c depending only on β; reason: uniform algorithms with the stated time bound; κ ≤ q under the hypothesis, so the unary κ does not change the bound
--   - encoding: outputs exactly the messages …; output list size at most ⌈2κbq/β⌉ → membership in both directions; output list length ≤ ⌈2κbq/β⌉; reason: set equality and size of the output list
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Theorem C.6, p.67 (PDF p.70); proof, p.68

import Mathlib
import Definitions.Def_LaconicBarrier_RunsWithin
import Definitions.Def_SeededShannon_Supplement_symCode

set_option autoImplicit false

namespace SeededShannon.Supplement

open LaconicBarrier

/-- **Theorem C.6 (Two-component Parvaresh–Vardy list recovery)** (Dujmovic, Lu, Silbak, Wichs,
*Shannon Rate Seeded Codes from Indistinguishability Obfuscation*, STOC 2027 submission (manuscript
sha256 52f4b606…a769709), Theorem C.6, p.67): fix `0 < β < 1`, let `λ, κ, b ≥ 1` be integers and
`k = λ + 1`, and let `q` be a power of two with `q ≥ max{8k/β, 256 κ b k²/β³}`. There is an
injective code `Encode_PV : {0,1}^λ → (𝔽_q²)^q` with deterministic construction, encoding and list
recovery in time `poly(λ, q, b)`. Given lists `U_x ⊆ 𝔽_q²`, indexed by `x ∈ 𝔽_q`, with
`W := Σ_x |U_x| ≤ κ · b · q²`, recovery outputs exactly the messages whose codewords `c` satisfy
`|{x ∈ 𝔽_q : c_x ∈ U_x}| ≥ β · q`; the output list has size at most `⌈2κbq/β⌉`.

**Formalization Note** The code and the recovery algorithm are functions of `(λ, q, κ, b)` (all
fixed before the code in the statement), computed by two fixed machines within `(λ + q + b + 2)^c`
steps on input `(1^λ, 1^q, 1^κ, 1^b, ·)`, for one exponent `c` depending only on `β`; the
construction of the field data is part of these computations. Field elements are named by `Fin q`
in binary, and the coordinates are indexed by `Fin q`; the field structure of `𝔽_q` does not enter
the statement. The recovery machine meets its time bound on every collection of lists; "outputs exactly" is
membership in both directions. -/
theorem theorem_C_6 (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ (enc : (lam q κ b : ℕ) → (Fin lam → Bool) → Fin q → Fin q × Fin q)
      (rec : (lam q κ b : ℕ) → (Fin q → Finset (Fin q × Fin q)) → List (Fin lam → Bool))
      (ME MR : KarpLiptonOM.OracleTM) (c : ℕ),
      ∀ lam κ b q : ℕ, 1 ≤ lam → 1 ≤ κ → 1 ≤ b → (∃ e : ℕ, q = 2 ^ e) →
        8 * ((lam + 1 : ℕ) : ℝ) / β ≤ q →
        256 * (κ : ℝ) * b * ((lam + 1 : ℕ) : ℝ) ^ 2 / β ^ 3 ≤ q →
        Function.Injective (enc lam q κ b) ∧
        (∀ x : Fin lam → Bool,
          RunsWithin ME [unary lam, unary q, unary κ, unary b, bits x]
            (pairWordCode (enc lam q κ b x)) ((lam + q + b + 2) ^ c)) ∧
        (∀ U : Fin q → Finset (Fin q × Fin q),
          RunsWithin MR [unary lam, unary q, unary κ, unary b, pairListsCode U]
            (QAdvFew.PoQOracle.tup ((rec lam q κ b U).map bits)) ((lam + q + b + 2) ^ c)) ∧
        ∀ U : Fin q → Finset (Fin q × Fin q), ∑ x, (U x).card ≤ κ * b * q ^ 2 →
          (∀ m : Fin lam → Bool, m ∈ rec lam q κ b U ↔
            β * q ≤ ((Finset.univ.filter (fun x => enc lam q κ b m x ∈ U x)).card : ℝ)) ∧
          ((rec lam q κ b U).length : ℝ) ≤ ⌈2 * κ * b * q / β⌉₊ := by sorry

end SeededShannon.Supplement
