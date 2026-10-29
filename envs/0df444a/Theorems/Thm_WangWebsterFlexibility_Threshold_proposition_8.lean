-- Prove2me | Theorems.Thm_WangWebsterFlexibility_Threshold_proposition_8
-- name    : WangWebsterFlexibility.Threshold.proposition_8
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:33:51.842899+00:00
-- url     : https://prove2.me/theorems/cea3b2d6-4a00-4d56-9783-62e22c92640a
-- title:
--   Proposition 8 — unique backup-cost threshold and primary-cost derivative
-- statement:
--   Fix arbitrary independent nonnegative demand laws, margins $\pi_1>\pi_2$, failure probability $0<\rho<1$, and exercise cost $0\le v<\pi_2$. There exists a real-valued threshold function $\Gamma(c)$ on $0\le c\le v$. At each such $c$, its value is the unique finite real number satisfying all four threshold clauses: at least one admissible fee lies below or at the cutoff; df weakly dominates ff for every such fee; ff weakly dominates df for every admissible fee above the cutoff; and strict ff dominance occurs for at least one fee above it. Admissibility means $\gamma\ge0$ and $\gamma+v>c$; the two networks optimize their reservations and primary orders independently.
--
--   For every $0<c<v$, a finite derivative exists and
--   $$\Gamma'(c)\le0.$$
--   At $c=0$ and $c=v$ a derivative within $[0,v]$ exists with a nonpositive value. The function's extension outside $[0,v]$ is unconstrained. For $v=0$ the interior clause is empty and the within-singleton derivative condition is vacuous; the unique threshold and all dominance clauses at $c=0$ remain required. No differentiability, bounded demand, unique optimizer, or single crossing is assumed.
--
--   This is an open statement of the full source result under the declared strong reading, not a machine-checked proof. Insight I2 records the source proof gap and insight I3 records failure of its strict-dominance clause for zero demands under the fixed-law reading.
--
--   Differences from the source:
--   - encoding: independent nonnegative real random demands and nonnegative real decisions → Borel probability laws on nonnegative reals, their product measure, and nonnegative-real decision types; reason: the law-based representation covers all the original distributions and decisions, including atoms and unbounded support
--   - encoding: separately optimized network profits → extended-real suprema over all feasible finite reservations and orders; reason: no boundedness or attainment assumption is supplied by the source; positive infinity must not become a default real zero
--   - reading: “for some γ+v≤Γ” on p. 21, versus “for any γ+v≤Γ” and the reverse weak inequality on A16 → all four strong single-crossing clauses with both existential witnesses, uniqueness at each c, fixed demand laws and fixed v while γ varies; reason: the weaker two-witness reading cannot characterize a unique cutoff; the appendix supplies the universal regime comparisons
--   - encoding: ∂Γ/∂c≤0 on the admissible cost domain → existence of a nonpositive ordinary derivative for 0<c<v and a nonpositive derivative within [0,v] at its endpoints; reason: the domain has boundary points and a total derivative default must not substitute for derivative existence; at v=0 only the singleton boundary convention applies
-- source:
--   Wang and Webster (2021), Product Flexibility Strategy Under Supply and Demand Risk, Manufacturing & Service Operations Management, https://doi.org/10.1287/msom.2021.1037, Proposition 8(a)–(b), printed/PDF p. 21; proof Appendix A2, printed A11–A16 / PDF 48–53

import Definitions.Def_WangWebsterFlexibility_Threshold_Cutoff
import Mathlib.Analysis.Calculus.Deriv.Basic

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


import Definitions.Def_WangWebsterFlexibility_Threshold_Profits

open scoped NNReal

namespace WangWebsterFlexibility.Threshold

/-- The strong single-crossing reading of Proposition 8(a) (p. 21 and A16).
Existence, uniqueness and regularity are deliberately not fields of the model. -/
def IsThreshold (M : Model) (c v Γ : ℝ) : Prop :=
  (∃ γ : ℝ, AdmissibleFee c v γ ∧ γ + v ≤ Γ) ∧
  (∀ γ : ℝ, AdmissibleFee c v γ → γ + v ≤ Γ →
    valueFF M c γ v ≤ valueDF M c γ v) ∧
  (∀ γ : ℝ, AdmissibleFee c v γ → Γ < γ + v →
    valueDF M c γ v ≤ valueFF M c γ v) ∧
  (∃ γ : ℝ, AdmissibleFee c v γ ∧ Γ < γ + v ∧
    valueDF M c γ v < valueFF M c γ v)

end WangWebsterFlexibility.Threshold

-/

namespace WangWebsterFlexibility.Threshold

/-- Proposition 8, p. 21, all clauses; the reading of some/any follows A16.
Ordinary derivatives are required inside [0,v], within-interval derivatives at its endpoints. -/
theorem proposition_8 (M : Model)
    (hπ : M.π₂ < M.π₁)
    (hρ₀ : 0 < M.ρ) (hρ₁ : M.ρ < 1)
    (v : ℝ) (hv : 0 ≤ v) (hvπ : v < M.π₂) :
    ∃ Γ : ℝ → ℝ,
      (∀ c ∈ Set.Icc 0 v, IsThreshold M c v (Γ c) ∧
        ∀ G : ℝ, IsThreshold M c v G → G = Γ c) ∧
      (∀ c ∈ Set.Ioo 0 v, ∃ a : ℝ, a ≤ 0 ∧ HasDerivAt Γ a c) ∧
      (∀ c : ℝ, c = 0 ∨ c = v →
        ∃ a : ℝ, a ≤ 0 ∧ HasDerivWithinAt Γ a (Set.Icc 0 v) c) := by sorry

end WangWebsterFlexibility.Threshold
