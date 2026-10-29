-- Prove2me | Theorems.Thm_WangWebsterFlexibility_Threshold_claim_A18
-- name    : WangWebsterFlexibility.Threshold.claim_A18
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:33:27.394883+00:00
-- url     : https://prove2.me/theorems/a9d4cce6-03fa-48f8-9e09-43d700ff5069
-- title:
--   Appendix A2, Claim (A-18) — finite backup-capacity witness
-- statement:
--   Let independent nonnegative demands and margins $\pi_1>\pi_2$ be fixed, with $0<\rho<1$ and $0\le c\le v<\pi_2$. There exist finite real numbers $\Gamma,\gamma$ such that $\gamma\ge0$, $c<\gamma+v\le\Gamma$, and finite feasible decisions $s^o,q_1,q_2\ge0$ satisfying
--   $$u_{df}(s^o,q_1,q_2;c,\gamma,v)\ge U_{ff}(c,\gamma,v).$$
--   The finite feasible df witness is part of the conclusion, even if the ff supremum is not attained. This is the claim attached to the displayed cumulative-benefit inequality (A-18), after cancelling the baseline terms. The source's infeasible zero-cost endpoint in its proof is recorded as insight I2; it is not an added hypothesis or a repaired target.
--
--   Differences from the source:
--   - encoding: independent nonnegative real random demands and nonnegative real decisions → Borel probability laws on nonnegative reals, their product measure, and nonnegative-real decision types; reason: the law-based representation covers all the original distributions and decisions, including atoms and unbounded support
--   - reading: the cost regime γ+v≤Γ immediately preceding the Claim (A-18) → an existential admissible reservation fee γ at fixed demand laws, margins, reliability, c and v; reason: makes the implicit cost regime and parameter dependence explicit while retaining the finite witnessing decisions
--   - encoding: the three baseline profit differences in (A-18) → u_df(sᵒ,q₁,q₂)≥U_ff after cancellation and replacing optimal ff notation by its value; reason: the finite df witness is preserved and the comparison does not presume an ff maximizer
--   - encoding: separately optimized network profits → extended-real suprema over all feasible finite reservations and orders; reason: no boundedness or attainment assumption is supplied by the source; positive infinity must not become a default real zero
-- source:
--   Wang and Webster (2021), Product Flexibility Strategy Under Supply and Demand Risk, Manufacturing & Service Operations Management, https://doi.org/10.1287/msom.2021.1037, Appendix A2, proof of Proposition 8, Claim associated with equation (A-18), printed A16 / PDF 53

import Definitions.Def_WangWebsterFlexibility_Threshold_Profits

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
import Mathlib.Data.EReal.Basic

open scoped NNReal

namespace WangWebsterFlexibility.Threshold

/-- Equation (4): independent primary failures, reservation paid up front, primary paid
on delivery including unsold units. Decisions are all nonnegative finite real numbers. -/
noncomputable def profitDF (M : Model) (c γ v : ℝ) (s q₁ q₂ : ℝ≥0) : ℝ :=
  -γ * (s : ℝ) - c * (1 - M.ρ) * ((q₁ : ℝ) + (q₂ : ℝ)) +
    M.ρ ^ 2 * M.expect (fun d => revenueDF M v d 0 0 s) +
    (1 - M.ρ) ^ 2 * M.expect (fun d => revenueDF M v d q₁ q₂ s) +
    M.ρ * (1 - M.ρ) * M.expect (fun d => revenueDF M v d q₁ 0 s) +
    M.ρ * (1 - M.ρ) * M.expect (fun d => revenueDF M v d 0 q₂ s)

/-- Equation (5): one common failure of the consolidated primary supplier. -/
noncomputable def profitFF (M : Model) (c γ v : ℝ) (s q : ℝ≥0) : ℝ :=
  -γ * (s : ℝ) - c * (1 - M.ρ) * (q : ℝ) +
    M.ρ * M.expect (fun d => revenueDF M v d 0 0 s) +
    (1 - M.ρ) * M.expect (fun d => revenueFF M v d q s)

/-- Independently optimized df value over the full feasible decision set, including zero.
The complete extended real order retains an unbounded supremum as positive infinity. -/
noncomputable def valueDF (M : Model) (c γ v : ℝ) : EReal :=
  ⨆ (s : ℝ≥0) (q₁ : ℝ≥0) (q₂ : ℝ≥0), (profitDF M c γ v s q₁ q₂ : EReal)

/-- Independently optimized ff value, with no assumed maximizer. -/
noncomputable def valueFF (M : Model) (c γ v : ℝ) : EReal :=
  ⨆ (s : ℝ≥0) (q : ℝ≥0), (profitFF M c γ v s q : EReal)

/-- Admissible reservation fee at fixed primary and exercise costs (§3, pp. 10–11). -/
def AdmissibleFee (c v γ : ℝ) : Prop := 0 ≤ γ ∧ c < γ + v

end WangWebsterFlexibility.Threshold

-/

namespace WangWebsterFlexibility.Threshold

/-- Appendix A2, Claim associated with (A-18), A16 (PDF 53): a finite feasible df
decision reaches the optimized ff value at some admissible cheap reservation fee. -/
theorem claim_A18 (M : Model)
    (hπ : M.π₂ < M.π₁)
    (hρ₀ : 0 < M.ρ) (hρ₁ : M.ρ < 1)
    (c v : ℝ) (hc : 0 ≤ c) (hcv : c ≤ v) (hvπ : v < M.π₂) :
    ∃ Γ γ : ℝ, AdmissibleFee c v γ ∧ γ + v ≤ Γ ∧
      ∃ s q₁ q₂ : ℝ≥0, valueFF M c γ v ≤ (profitDF M c γ v s q₁ q₂ : EReal) := by sorry

end WangWebsterFlexibility.Threshold
