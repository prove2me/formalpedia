-- Prove2me | Theorems.Thm_SeededShannon_theorem_3_14
-- name    : SeededShannon.theorem_3_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T05:23:01.204654+00:00
-- url     : https://prove2.me/theorems/48b4e7d0-9cf3-44a8-894d-e22d284295d6
-- title:
--   Theorem 3.14 — codes for balanced errors
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Fix constants $0<\tau<1/2$, $0<\zeta<1-H(\tau)$ and $\gamma>0$ with $C\sqrt\gamma\le\zeta$. For every sufficiently large fixed integer $b$ and every sufficiently large $n$ divisible by $b$, there is an injective binary-linear code
--   $$\mathrm{Encode}_n:\{0,1\}^{k(n)}\to\{0,1\}^n,\qquad \frac{k(n)}{n}\ge 1-H(\tau)-\zeta,$$
--   that is $L(n)$-list decodable against $(b,\tau,\gamma)$-balanced errors (Definition 3.13), with $L(n)=\mathrm{poly}(n)$. Construction, encoding and list decoding are deterministic and take time $\mathrm{poly}(n)$.
--
--   The balanced-error code is the outer code of Construction 6.1 and fixes its rate.
--
--   **Formalization Note** $H$ is the binary entropy in bits (`WildeQIT.binaryEntropy`).
--
--   Differences from the source:
--   - encoding: binary-linear code → Encode_n(x ⊕ y) = Encode_n(x) ⊕ Encode_n(y); reason: additivity over 𝔽₂ is linearity
--   - encoding: every sufficiently large fixed integer b and every sufficiently large n divisible by b → ∃ b₀, ∀ b ≥ b₀, ∃ n₀, ∀ n ≥ n₀ with b ∣ n; reason: standard meaning; C is absolute, chosen before τ, ζ, γ
--   - encoding: construction, encoding, list decoding deterministic in time poly(n) → one polynomial-time machine each on input 1^n (construction outputs 1^{k(n)}), for all supported n; reason: uniform construction of the family
--   - encoding: H, the binary entropy function → WildeQIT.binaryEntropy, logarithm base 2; reason: same function
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Theorem 3.14, p.21 (PDF p.24)

import Mathlib
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_SeededShannon_balP

set_option autoImplicit false

namespace SeededShannon

open LaconicBarrier NoisyOWMPC

/-- **Theorem 3.14 (Codes for Balanced Errors)** (Dujmovic, Lu, Silbak, Wichs, STOC 2027 submission
(manuscript sha256 52f4b606…a769709), Theorem 3.14, p.21): there is an absolute constant `C > 0`
such that, for constants `0 < τ < 1/2`, `0 < ζ < 1 − H(τ)` and `γ > 0` with `C√γ ≤ ζ`, for every
sufficiently large fixed integer `b` and every sufficiently large `n` divisible by `b`, there is an
injective binary-linear code of rate at least `1 − H(τ) − ζ` that is `L(n)`-list decodable against
`(b, τ, γ)`-balanced errors, with `L(n) = poly(n)`; construction, encoding and list decoding are
deterministic and take time `poly(n)`.

**Formalization Note** `H` is the binary entropy in bits (`WildeQIT.binaryEntropy`). The code at
length `n` is `enc n : {0,1}^{k(n)} → {0,1}^n`, binary-linear meaning additive over `𝔽₂` (bitwise
xor). "Sufficiently large" is `∃ b₀, ∀ b ≥ b₀` and `∃ n₀, ∀ n ≥ n₀`. Construction, encoding and
decoding are one machine each, run on `1^n` (construction outputs `1^{k(n)}`). -/
theorem theorem_3_14 :
    ∃ C : ℝ, 0 < C ∧ ∀ τ ζ γ : ℝ, 0 < τ → τ < 1 / 2 → 0 < ζ →
      ζ < 1 - WildeQIT.binaryEntropy τ → 0 < γ → C * Real.sqrt γ ≤ ζ →
      ∃ b₀ : ℕ, ∀ b ≥ b₀, ∃ (n₀ : ℕ) (k L : ℕ → ℕ)
        (enc : (n : ℕ) → (Fin (k n) → Bool) → Fin n → Bool)
        (dec : (n : ℕ) → (Fin n → Bool) → List (Fin (k n) → Bool)),
        PolyBounded L ∧
        (∀ n ≥ n₀, b ∣ n →
          Function.Injective (enc n) ∧
          (∀ x y : Fin (k n) → Bool,
            enc n (fun i => xor (x i) (y i)) = fun j => xor (enc n x j) (enc n y j)) ∧
          1 - WildeQIT.binaryEntropy τ - ζ ≤ (k n : ℝ) / n ∧
          BalancedListDecodable b τ γ (enc n) (dec n) (L n)) ∧
        PolyTimeOn (ι := {n : ℕ // n₀ ≤ n ∧ b ∣ n}) (fun n => [unary n.1]) (fun n => unary (k n.1)) ∧
        PolyTimeOn (ι := (n : {n : ℕ // n₀ ≤ n ∧ b ∣ n}) × (Fin (k n.1) → Bool))
          (fun i => [unary i.1.1, bits i.2]) (fun i => bits (enc i.1.1 i.2)) ∧
        PolyTimeOn (ι := (n : {n : ℕ // n₀ ≤ n ∧ b ∣ n}) × (Fin n.1 → Bool))
          (fun i => [unary i.1.1, bits i.2])
          (fun i => QAdvFew.PoQOracle.tup ((dec i.1.1 i.2).map bits)) := by sorry

end SeededShannon
