-- Prove2me | Theorems.Thm_TimeInconsLQ_Deterministic_theorem_4_3
-- name    : TimeInconsLQ.Deterministic.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:25:08.086245+00:00
-- url     : https://prove2.me/theorems/afba97f3-4b19-49f4-9f7a-9feac53bc180
-- title:
--   Theorem 4.3 — singular case R ≡ 0: (4.13) and (4.9) admit positive solution pairs
-- statement:
--   Consider the scalar-state problem with deterministic coefficients of §4 under the standing assumptions, with $\Gamma^{(1)}_s=\mu_1e^{\int_s^TA_r\,dr}$.
--
--   **Theorem 4.3 (singular case).** Assume $G\ge h>0$, $R\equiv0$ on $[0,T]$ and $D'D-\delta I\succeq0$ on $[0,T]$ for some $\delta>0$. If, on $[0,T]$,
--   $$Q+\Gamma^{(1)}B'(D'D)^{-1}(B+D'C)\ge0\qquad\text{and}\qquad Q+\Gamma^{(1)}B'(D'D)^{-1}D'C\ge0,$$
--   then the system (4.13) and the system (4.9) admit positive solution pairs on $[0,T]$.
--
--   When the control carries no running cost, the noise must act nondegenerately on the control; this theorem gives solvability of the Riccati system in that case. It asserts existence only.
--
--   **Formalization Note.** Solutions are in integral form on $[0,T]$; a solution of (4.13) includes invertibility of $D_s'D_s$ on $[0,T]$.
-- source:
--   Hu, Jin, Zhou, Time-Inconsistent Stochastic Linear–Quadratic Control, arXiv:1111.0818v1, p. 13, Theorem 4.3

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_Deterministic_Model
import Definitions.Def_TimeInconsLQ_Deterministic_Riccati

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal NNReal

namespace TimeInconsLQ.Deterministic

/-- Theorem 4.3 (p. 13, singular case): if `G ≥ h > 0`, `R ≡ 0`, `D′D − δI ⪰ 0` for some
`δ > 0`, `Q + Γ⁽¹⁾B′(D′D)⁻¹(B + D′C) ≥ 0` and `Q + Γ⁽¹⁾B′(D′D)⁻¹D′C ≥ 0` on `[0, T]`, then
(4.13) and (4.9) admit positive solution pairs on `[0, T]`. -/
theorem theorem_4_3 {l d : ℕ} (c : Coeffs l d) (T : ℝ≥0) (hT : 0 < T)
    (hc : CoeffsStanding c T) (hGh : c.h ≤ c.G) (hh : 0 < c.h)
    (hR0 : ∀ s ≤ T, c.R s = 0) (hD : DNondeg c T)
    (hQ1 : ∀ s ≤ T, 0 ≤ c.Q s + Gam1 c T s * (c.B s ⬝ᵥ (KD c s *ᵥ BDC c s)))
    (hQ2 : ∀ s ≤ T, 0 ≤ c.Q s + Gam1 c T s * (c.B s ⬝ᵥ (KD c s *ᵥ DtC c s))) :
    (∃ M J, IsPosSol413 c T M J) ∧ (∃ M N, IsPosSol49 c T M N) := by sorry

end TimeInconsLQ.Deterministic
