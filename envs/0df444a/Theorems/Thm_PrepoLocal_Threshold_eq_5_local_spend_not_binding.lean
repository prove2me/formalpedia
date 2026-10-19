-- Prove2me | Theorems.Thm_PrepoLocal_Threshold_eq_5_local_spend_not_binding
-- name    : PrepoLocal.Threshold.eq_5_local_spend_not_binding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:57.060604+00:00
-- url     : https://prove2.me/theorems/265871f8-a1e3-4a33-baeb-26b5ac1dd938
-- title:
--   §4.1, pp. 9–10, at (5) — if b ≥ b̄, the local spend constraint does not bind for 0 ≤ x ≤ (x₊)⁺, so S(x) = (D − Q)⁺ a.s.
-- statement:
--   In the single-cycle prepo model (standing assumptions as in the model definition), let $x_+=\bar F^{-1}_{D-Q}(\beta^*)$ be a net-demand fractile as in eq. (4). The paper's threshold budget is
--   $$
--   \bar b=\max\{\alpha\min\{d,q\}-r:(d,q,r)\in\Omega\}-\gamma\underline T+(x_+)^+, \tag{5}
--   $$
--   where $\underline T$ is the lower end of the support of $T$. Suppose $b\ge\bar b$, in the following form: there are numbers $M$ and $T_{lo}$ with $\alpha\min\{D,Q\}-R\le M$ almost surely, $T\ge T_{lo}$ almost surely, and
--   $$
--   M-\gamma T_{lo}+(x_+)^+\le b .
--   $$
--   Then for every prepo level $x$ with $0\le x\le (x_+)^+$ and $x\le b$, the local spend constraint is not binding: almost surely
--   $$
--   \min\{D,Q\}\le\hat b(x,R,T)/\alpha,
--   $$
--   and consequently, almost surely, $S(x)=(D-Q)^+$.
--
--   Above the threshold the HO always has enough money to buy whatever local supply the demand calls for, so the local shortage is the shortage of local supply alone; this is what reduces problem $\Pi$ to the auxiliary model.
--
--   **Formalization Note** The maximum over the support in (5) is encoded through almost-sure bounds. This is equivalent to $b\ge\bar b$: take $M$ the maximum in (5) and $T_{lo}=\underline T$; conversely, any such $M$, $T_{lo}$ satisfy $M\ge\max\{\ldots\}$ and $T_{lo}\le\underline T$, so $\bar b\le M-\gamma T_{lo}+(x_+)^+\le b$ because $\gamma\ge0$. No supremum appears in the statement.
-- source:
--   Eftekhar, Song & Webster, Pre-Positioning and Local-Purchasing for Emergency Operations Under Budget and Supply Uncertainty, SSRN 3210309 (revision of Aug. 13, 2020), pp. 9–10, §4.1, eq. (5) and the sentence containing it

import Mathlib
import Definitions.Def_PrepoLocal_Threshold_Model
open MeasureTheory ProbabilityTheory

namespace PrepoLocal.Threshold

/-- §4.1, pp. 9–10, at (5): if the budget is at least
`b̄ = max{α min{d,q} − r} − γT̲ + (x₊)⁺` (encoded through an a.s. upper bound `M` on
`α min{D,Q} − R` and an a.s. lower bound `Tlo` on `T`), then for every feasible prepo level
`0 ≤ x ≤ (x₊)⁺` the local spend constraint does not bind: a.s. `min{D,Q} ≤ b̂(x,R,T)/α`,
and hence a.s. `S(x) = (D − Q)⁺`. -/
theorem eq_5_local_spend_not_binding {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (P : Params) (hP : P.Standing) (E : Env Ω) (hE : E.Standing μ)
    (xplus : ℝ) (hx : IsNetFractile μ E (betaStar P μ E) xplus)
    (M Tlo : ℝ) (hM : ∀ᵐ ω ∂μ, P.al * min (E.D ω) (E.Q ω) - E.R ω ≤ M)
    (hT : ∀ᵐ ω ∂μ, Tlo ≤ E.T ω)
    (hb : M - P.gam * Tlo + max xplus 0 ≤ P.b)
    (x : ℝ) (hx0 : 0 ≤ x) (hxp : x ≤ max xplus 0) (hxb : x ≤ P.b) :
    (∀ᵐ ω ∂μ, min (E.D ω) (E.Q ω) ≤ bhat P E x ω / P.al) ∧
      (∀ᵐ ω ∂μ, S P E x ω = max (E.D ω - E.Q ω) 0) := by sorry

end PrepoLocal.Threshold
