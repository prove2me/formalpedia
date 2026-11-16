-- Prove2me | Theorems.Thm_SeededShannon_Supplement_theorem_C_4
-- name    : SeededShannon.Supplement.theorem_C_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:48:27.256573+00:00
-- url     : https://prove2.me/theorems/8beccdfe-4836-4af5-afa4-3683fd28a9f2
-- title:
--   Theorem C.4 — concatenated Reed–Solomon list recovery
-- statement:
--   Fix $0<p<1$, let $\alpha=(1-p)/(1+p)$, and let $q$ be a prime power satisfying
--   $$q\ge\max\Big\{2,\ \frac1p,\ \frac{2\lambda}{\alpha^3}\Big\}.$$
--   There is an injective code $\mathrm{Encode}_{\lambda,q}:\{0,1\}^\lambda\to\mathbb F_q^{q^3}$ with deterministic encoding and list recovery in time $\mathrm{poly}(\lambda,q)$. For every collection of lists $T_i\subseteq\mathbb F_q$, $i\in[q^3]$, with total size at most $\lfloor p\cdot q^4\rfloor$, recovery outputs exactly the messages whose encodings agree with every list ($\mathrm{Encode}_{\lambda,q}(x)_i\in T_i$ for all $i$), and the output has size at most $2q^2$.
--
--   This code instantiates the sparse-set embedding of Corollary 5.9 behind the sparse-set obfuscator of Construction 6.1.
--
--   **Formalization Note** One encoding machine and one recovery machine, with a running-time exponent depending only on $p$, work for all $(\lambda,q)$ on input $(1^\lambda,1^q,\cdot)$.
--
--   Differences from the source:
--   - encoding: 𝔽_q and codewords in 𝔽_q^{q³}; lists T_i ⊆ 𝔽_q → the alphabet Fin q with binary symbol codes (symCode); words Fin (q³) → Fin q; reason: the field structure does not enter the statement; any representation of 𝔽_q is in polynomial-time bijection with Fin q
--   - encoding: deterministic encoding and list recovery in time poly(λ, q) → two fixed machines (LaconicBarrier.RunsWithin) halting within (λ + q + 2)^c steps on (1^λ, 1^q, input), c depending only on p; reason: uniform algorithms with the stated time bound
--   - encoding: outputs exactly the messages …, the output has size at most 2q² → membership in both directions; output list length ≤ 2q²; reason: set equality and size of the output list
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Theorem C.4, p.66 (PDF p.69); Construction C.5, pp.66–67

import Mathlib
import Definitions.Def_LaconicBarrier_RunsWithin
import Definitions.Def_SeededShannon_Supplement_symCode

set_option autoImplicit false

namespace SeededShannon.Supplement

open LaconicBarrier

/-- **Theorem C.4 (Concatenated Reed–Solomon list recovery)** (Dujmovic, Lu, Silbak, Wichs, *Shannon
Rate Seeded Codes from Indistinguishability Obfuscation*, STOC 2027 submission (manuscript sha256
52f4b606…a769709), Theorem C.4, p.66): fix `0 < p < 1`, let `α = (1 − p)/(1 + p)`, and let `q` be a
prime power with `q ≥ max{2, 1/p, 2λ/α³}`. There is an injective code
`Encode_{λ,q} : {0,1}^λ → 𝔽_q^{q³}` with deterministic encoding and list recovery in time
`poly(λ, q)`. For every collection of lists `T_i ⊆ 𝔽_q`, `i ∈ [q³]`, of total size at most
`⌊p · q⁴⌋`, recovery outputs exactly the messages whose encodings agree with every list, and the
output has size at most `2q²`.

**Formalization Note** The code and the recovery algorithm are functions of `(λ, q)`, computed by
two fixed machines (the published `LaconicBarrier.RunsWithin` model) within `(λ + q + 2)^c` steps on
input `(1^λ, 1^q, ·)`, for one exponent `c` depending only on `p`. Field elements are named by
`Fin q` in binary (`symCode`); the field structure of `𝔽_q` does not enter the statement.
The recovery machine meets its time bound on every collection of lists; "outputs exactly" is
membership in both directions; the output size is the length of the output
list. -/
theorem theorem_C_4 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ (enc : (lam q : ℕ) → (Fin lam → Bool) → Fin (q ^ 3) → Fin q)
      (rec : (lam q : ℕ) → (Fin (q ^ 3) → Finset (Fin q)) → List (Fin lam → Bool))
      (ME MR : KarpLiptonOM.OracleTM) (c : ℕ),
      ∀ lam q : ℕ, IsPrimePow q → (2 : ℝ) ≤ q → 1 / p ≤ q →
        2 * lam / ((1 - p) / (1 + p)) ^ 3 ≤ (q : ℝ) →
        Function.Injective (enc lam q) ∧
        (∀ x : Fin lam → Bool,
          RunsWithin ME [unary lam, unary q, bits x] (wordCode (enc lam q x)) ((lam + q + 2) ^ c)) ∧
        (∀ T : Fin (q ^ 3) → Finset (Fin q),
          RunsWithin MR [unary lam, unary q, listsCode T]
            (QAdvFew.PoQOracle.tup ((rec lam q T).map bits)) ((lam + q + 2) ^ c)) ∧
        ∀ T : Fin (q ^ 3) → Finset (Fin q), ∑ i, (T i).card ≤ ⌊p * (q : ℝ) ^ 4⌋₊ →
          (∀ x : Fin lam → Bool, x ∈ rec lam q T ↔ ∀ i, enc lam q x i ∈ T i) ∧
          (rec lam q T).length ≤ 2 * q ^ 2 := by sorry

end SeededShannon.Supplement
