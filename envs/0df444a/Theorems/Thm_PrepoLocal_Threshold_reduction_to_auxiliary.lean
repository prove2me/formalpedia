-- Prove2me | Theorems.Thm_PrepoLocal_Threshold_reduction_to_auxiliary
-- name    : PrepoLocal.Threshold.reduction_to_auxiliary
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:52.379245+00:00
-- url     : https://prove2.me/theorems/3d89f95a-752f-40fe-9513-7d01da991986
-- title:
--   §4.1, p. 10 — if b ≥ b̄, problem Π reduces to the auxiliary model: C(x) = Ca(x) for x ∈ [0, min{(x₊)⁺, b}]
-- statement:
--   In the single-cycle prepo model (standing assumptions as in the model definition), let $x_+=\bar F^{-1}_{D-Q}(\beta^*)$ be a net-demand fractile as in eq. (4), and suppose $b\ge\bar b$ of (5), in the form: $\alpha\min\{D,Q\}-R\le M$ a.s., $T\ge T_{lo}$ a.s., and $M-\gamma T_{lo}+(x_+)^+\le b$. Then the expected cycle cost of problem $\Pi$ equals the auxiliary cost on the feasible levels up to $\bar x^*=\min\{(x_+)^+,b\}$:
--   $$
--   C(x)=C_a(x)\qquad\text{for every }x\in\bigl[0,\min\{(x_+)^+,b\}\bigr].
--   $$
--
--   This is the paper's statement that, by comparing $b$ with $\bar b$, problem $\Pi$ reduces to the auxiliary model.
--
--   **Formalization Note** The threshold $b\ge\bar b$ is encoded through the almost-sure bounds $M$, $T_{lo}$, which is equivalent (see the Formalization Note of the non-binding statement at (5)).
-- source:
--   Eftekhar, Song & Webster, Pre-Positioning and Local-Purchasing for Emergency Operations Under Budget and Supply Uncertainty, SSRN 3210309 (revision of Aug. 13, 2020), p. 10, §4.1, sentence after (5)

import Mathlib
import Definitions.Def_PrepoLocal_Threshold_Model
open MeasureTheory ProbabilityTheory

namespace PrepoLocal.Threshold

/-- §4.1, p. 10: if `b ≥ b̄` (encoded as in (5) through a.s. bounds `M`, `Tlo`), problem Π
reduces to the auxiliary model on the feasible levels up to `x̄∗`:
`C(x) = Ca(x)` for every `x ∈ [0, min{(x₊)⁺, b}]`. -/
theorem reduction_to_auxiliary {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (P : Params) (hP : P.Standing) (E : Env Ω) (hE : E.Standing μ)
    (xplus : ℝ) (hx : IsNetFractile μ E (betaStar P μ E) xplus)
    (M Tlo : ℝ) (hM : ∀ᵐ ω ∂μ, P.al * min (E.D ω) (E.Q ω) - E.R ω ≤ M)
    (hT : ∀ᵐ ω ∂μ, Tlo ≤ E.T ω)
    (hb : M - P.gam * Tlo + max xplus 0 ≤ P.b) :
    ∀ x ∈ Set.Icc 0 (min (max xplus 0) P.b), C P μ E x = Ca P μ E x := by sorry

end PrepoLocal.Threshold
