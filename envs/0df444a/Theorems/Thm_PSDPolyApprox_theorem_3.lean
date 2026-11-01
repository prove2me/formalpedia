-- Prove2me | Theorems.Thm_PSDPolyApprox_theorem_3
-- name    : PSDPolyApprox.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:52:31.845545+00:00
-- url     : https://prove2.me/theorems/1492e03a-5ba8-4d54-9bc7-9633e8fe4c8d
-- title:
--   Theorem 3 — hypercontractivity of the noise operator (Bonami–Beckner): $\|T_\rho f\|_q\le\|f\|_p$, $q=1+\rho^{-2}(p-1)$
-- statement:
--   **Theorem 3 (Hypercontractivity of the noise operator on the hypercube; Bonami, Beckner).** For every $n$, every $0<\rho\le1$, every $f:H_n\to\mathbb R$ and every real $p\ge1$, with
--   $$
--   q=1+\rho^{-2}(p-1),
--   $$
--   we have
--   $$
--   \|T_\rho f\|_q\le\|f\|_p\qquad\text{and}\qquad q\ge p .
--   $$
--   Here $\|g\|_s=(\mathbb E_{x\sim\mu}|g(x)|^s)^{1/s}$ with $\mu$ uniform on $H_n$. The inequality says that the smoothed function $T_\rho f$ is much flatter than $f$; Lemma 1 combines it with Markov's inequality.
--
--   Differences from the source:
--   - encoding: q = 1 + ρ^{−2}(p − 1) ≥ p → the inequality and q ≥ p as two conjuncts; reason: the printed "≥ p" is part of the statement
--   - encoding: H_n = {−1, 1}^n and the uniform measure µ → functions Fin n → ℤˣ; µ(S) = |S|/2^n and E[f] = 2^{−n} Σ f; reason: ℤˣ = {±1}; same instances
-- source:
--   Fawzi, On polyhedral approximations of the positive semidefinite cone, arXiv:1811.09649v1, Theorem 3, p.3 (citing [Bon70, Bec75])

import Mathlib
import Definitions.Def_PSDPolyApprox_noise
import Definitions.Def_PSDPolyApprox_lpNorm

namespace PSDPolyApprox

/-- **Theorem 3 (Hypercontractivity of the noise operator on the hypercube; Bonami, Beckner).**
Fawzi, arXiv:1811.09649v1, Theorem 3, p.3 ([Bon70, Bec75]): "For any 0 < ρ ≤ 1, f : Hn → R, and
p ≥ 1 we have ∥Tρf∥q ≤ ∥f∥p where q = 1 + ρ−2(p − 1) ≥ p."

For every `n`, `0 < ρ ≤ 1`, `f : Hₙ → ℝ` and real `p ≥ 1`, with `q = 1 + ρ⁻²(p − 1)`:
`‖T_ρ f‖_q ≤ ‖f‖_p` and `q ≥ p`. -/
theorem theorem_3 (n : ℕ) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (f : Cube n → ℝ) (p : ℝ)
    (hp : 1 ≤ p) :
    lpNorm (1 + (ρ ^ 2)⁻¹ * (p - 1)) (noise ρ f) ≤ lpNorm p f ∧
      p ≤ 1 + (ρ ^ 2)⁻¹ * (p - 1) := by sorry

end PSDPolyApprox
