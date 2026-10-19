-- Prove2me | Theorems.Thm_SeqDiagnosis_BeliefRecon_tcal_zero
-- name    : SeqDiagnosis.BeliefRecon.tcal_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:57.567883+00:00
-- url     : https://prove2.me/theorems/f07ed804-0ee0-4189-ae9f-55f276629f23
-- title:
--   Proof of Theorem 1, p. ec1 — baseline coordinate and total mass
-- statement:
--   Let $\theta$ be a probability vector and let $\mathcal T^t(x,\theta)$ be the reconstruction transform from equation (3). Its baseline component can be written as
--
--   $$\mathcal T_0^t(x,\theta)=\frac{\theta_0}{\theta_0+\sum_{i=1}^{N}\theta_i\exp\{t(\beta_{i0}+e_i\mathbb R x)\}},\qquad \sum_{j=0}^{N}\mathcal T_j^t(x,\theta)=1.$$
--
--   The theorem makes the paper's residual definition of class zero agree with the same normalized denominator as the other classes, so the reconstructed vector has total mass one.
--
--   **Formalization Note** The model's standing density assumptions are explicit. The prior may assign zero mass to class zero; the denominator is still positive because the prior sums to one and exponential factors are positive.
-- source:
--   Wang, Optimal Sequential Multi-class Diagnosis, arXiv:1506.08915v4, p. ec1 (PDF 38), proof of Theorem 1, final paragraph

import Mathlib
import Definitions.Def_SeqDiagnosis_BeliefRecon_Model

open Matrix

namespace SeqDiagnosis.BeliefRecon

/-- The baseline coordinate is the residual mass, giving total reconstructed mass one. -/
theorem tcal_zero {Y : Type*} [MeasurableSpace Y] {N p r : ℕ}
    (M : Model Y N p) (hS : M.Standing) (hETM : M.ETM)
    (R : Matrix (Fin N) (Fin r) ℝ) (P : Matrix (Fin r) (Fin p) ℝ)
    (θ : Fin (N + 1) → ℝ) (hθ : θ ∈ stdSimplex ℝ (Fin (N + 1)))
    (t : ℕ) (x : Fin r → ℝ) :
    Tcal M R P t x θ 0 = θ 0 /
      (θ 0 + ∑ i : Fin N, θ i.succ * Real.exp ((t : ℝ) * (betaZero M R P i + (R *ᵥ x) i))) ∧
    (∑ k, Tcal M R P t x θ k) = 1 := by sorry

end SeqDiagnosis.BeliefRecon
