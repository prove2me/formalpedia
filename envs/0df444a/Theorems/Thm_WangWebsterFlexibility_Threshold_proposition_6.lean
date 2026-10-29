-- Prove2me | Theorems.Thm_WangWebsterFlexibility_Threshold_proposition_6
-- name    : WangWebsterFlexibility.Threshold.proposition_6
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:33:32.53552+00:00
-- url     : https://prove2.me/theorems/62893b7e-0ba2-4d21-83a5-08e34df40422
-- title:
--   Proposition 6 — vanishing benefit regimes
-- statement:
--   Let $D_1,D_2$ be independent nonnegative demands, $\pi_1>\pi_2\ge0$, $0\le\rho\le1$, and $v\ge0$. For every nonnegative real reservation $s$ and primary orders $q_1,q_2$, both conclusions are asserted:
--   $$D_1\text{ is deterministic}\ \Longrightarrow\ DP(s,q_1,q_2)=0,$$
--   $$s=0\ \text{or}\ s=\operatorname{ess\,sup}(D_1+D_2)\ \Longrightarrow\ SD(s,q_1,q_2)=0.$$
--   The second branch refers only to a finite essential upper endpoint. The first clause retains the printed unrestricted orders; it does not assume $q_1$ equals deterministic demand or that the orders are optimal. Its counterexample is recorded separately in insight I1. The source uses part (b) in the threshold argument.
--
--   Differences from the source:
--   - encoding: independent nonnegative real random demands and nonnegative real decisions → Borel probability laws on nonnegative reals, their product measure, and nonnegative-real decision types; reason: the law-based representation covers all the original distributions and decisions, including atoms and unbounded support
--   - encoding: max{D₁+D₂} → finite essential upper endpoint characterized by an almost-sure upper bound and positive upper tails below it; reason: a distributional support maximum is represented without assuming bounded demand globally
--   - encoding: standing nonnegative costs with v≥c and γ+v>c → only v≥0 appears because DP and SD do not depend on c or γ; reason: every v≥0 extends to standing costs, for example c=0 and γ=1; this removes no instance and adds no benefit-function instance
-- source:
--   Wang and Webster (2021), Product Flexibility Strategy Under Supply and Demand Risk, Manufacturing & Service Operations Management, https://doi.org/10.1287/msom.2021.1037, Proposition 6, printed/PDF p. 18; proof printed A8–A9 / PDF 45–46

import Definitions.Def_WangWebsterFlexibility_Threshold_Benefits

open scoped NNReal

/- Imported definition bodies for the blind statement audit.
These are quotations of the imported Lean modules, not new declarations.

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

open scoped NNReal

namespace WangWebsterFlexibility.Threshold

/-- Two independent nonnegative demand laws and the common economic primitives (§3, pp. 9–11).
The laws are unrestricted Borel probability measures; no moment or density is assumed. -/
structure Model where
  demand₁ : ProbabilityMeasure ℝ≥0
  demand₂ : ProbabilityMeasure ℝ≥0
  π₁ : ℝ
  π₂ : ℝ
  ρ : ℝ

/-- Independence is implemented with the standard product measure. -/
noncomputable def Model.law (M : Model) : Measure (ℝ≥0 × ℝ≥0) :=
  (M.demand₁ : Measure ℝ≥0).prod (M.demand₂ : Measure ℝ≥0)

/-- Expected value under the independent demand laws. The sales expressions used below are
measurable and bounded for each fixed finite decision, even when demand has infinite mean. -/
noncomputable def Model.expect (M : Model) (f : ℝ≥0 × ℝ≥0 → ℝ) : ℝ :=
  ∫ d, f d ∂M.law

/-- Real positive part, used in the printed allocation formulas. -/
noncomputable def pos (x : ℝ) : ℝ := max 0 x

/-- Revenue net of exercise charges with dedicated available primary quantities (4), p. 12. -/
noncomputable def revenueDF (M : Model) (v : ℝ) (d : ℝ≥0 × ℝ≥0)
    (a₁ a₂ s : ℝ) : ℝ :=
  M.π₁ * min (d.1 : ℝ) a₁ + M.π₂ * min (d.2 : ℝ) a₂ +
    (M.π₁ - v) * min (pos ((d.1 : ℝ) - a₁)) s +
    (M.π₂ - v) * min (pos ((d.2 : ℝ) - a₂)) (pos (s - pos ((d.1 : ℝ) - a₁)))

/-- Revenue net of exercise charges when the flexible primary succeeds (5), p. 13. -/
noncomputable def revenueFF (M : Model) (v : ℝ) (d : ℝ≥0 × ℝ≥0)
    (q s : ℝ) : ℝ :=
  M.π₁ * min (d.1 : ℝ) q + M.π₂ * min (d.2 : ℝ) (pos (q - (d.1 : ℝ))) +
    (M.π₁ - v) * min (pos ((d.1 : ℝ) - q)) s +
    (M.π₂ - v) * min (pos ((d.2 : ℝ) - pos (q - (d.1 : ℝ))))
      (pos (s - pos ((d.1 : ℝ) - q)))

end WangWebsterFlexibility.Threshold


import Definitions.Def_WangWebsterFlexibility_Threshold_Model

open MeasureTheory

open scoped NNReal

namespace WangWebsterFlexibility.Threshold

/-- Demand pooling benefit at the same total primary order (§4.2, p. 18; A7). -/
noncomputable def DP (M : Model) (v : ℝ) (s q₁ q₂ : ℝ≥0) : ℝ :=
  (1 - M.ρ) * M.expect (fun d =>
    revenueFF M v d ((q₁ : ℝ) + (q₂ : ℝ)) s - revenueDF M v d q₁ q₂ s)

/-- Supplier diversification benefit from the four backup allocations (p. 18; A7–A8).
Neither primary cost nor reservation fee occurs in this expression. -/
noncomputable def SD (M : Model) (v : ℝ) (s q₁ q₂ : ℝ≥0) : ℝ :=
  (M.π₂ - v) * M.ρ * (1 - M.ρ) * M.expect (fun d =>
    let A := pos ((s : ℝ) - pos ((d.1 : ℝ) - (q₁ : ℝ)))
    let B := pos ((s : ℝ) - (d.1 : ℝ))
    min A (d.2 : ℝ) - min A (pos ((d.2 : ℝ) - (q₂ : ℝ))) +
      min B (pos ((d.2 : ℝ) - (q₂ : ℝ))) - min B (d.2 : ℝ))

/-- Product 1 is almost surely constant, including the zero constant. -/
def DeterministicFirst (M : Model) : Prop :=
  ∃ a : ℝ≥0, ∀ᵐ d ∂(M.demand₁ : Measure ℝ≥0), d = a

/-- Finite essential upper endpoint of total demand, interpreting max{D₁+D₂} in
Proposition 6(b). This predicate is simply false for every finite s if support is unbounded. -/
def TotalDemandEndpoint (M : Model) (s : ℝ≥0) : Prop :=
  (∀ᵐ d ∂M.law, (d.1 : ℝ) + (d.2 : ℝ) ≤ (s : ℝ)) ∧
    ∀ t : ℝ, t < (s : ℝ) → 0 < M.law {d | t < (d.1 : ℝ) + (d.2 : ℝ)}

end WangWebsterFlexibility.Threshold

-/

namespace WangWebsterFlexibility.Threshold

/-- Proposition 6, p. 18, both clauses with the printed unrestricted order quantities. -/
theorem proposition_6 (M : Model)
    (hπ₂ : 0 ≤ M.π₂) (hπ : M.π₂ < M.π₁)
    (hρ₀ : 0 ≤ M.ρ) (hρ₁ : M.ρ ≤ 1)
    (v : ℝ) (hv : 0 ≤ v) (s q₁ q₂ : ℝ≥0) :
    (DeterministicFirst M → DP M v s q₁ q₂ = 0) ∧
    (s = 0 ∨ TotalDemandEndpoint M s → SD M v s q₁ q₂ = 0) := by sorry

end WangWebsterFlexibility.Threshold
