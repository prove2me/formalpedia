-- Prove2me | Theorems.Thm_PushInfoShare_proposition_1
-- name    : PushInfoShare.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:48:59.55054+00:00
-- url     : https://prove2.me/theorems/0ff2bea5-34c8-47d5-8a81-12378212b738
-- title:
--   Proposition 1, p.11 — the equilibrium prices and orders (corrected: two index slips in $q_i$)
-- statement:
--   Let $\phi\ge0$ and fix the sharing decisions $\delta$. A profile is a linear separating equilibrium if and only if, for each $i$, its price rule is
--   $$w_i=\frac{\bigl(2+3\phi-\tfrac{S_{3-i}}{B_{3-i}}\bar\delta_{3-i}\bigr)a}{\bigl(2(1+\phi)-\tfrac{S_i}{B_i}\bar\delta_i\bigr)\bigl(2(1+\phi)-\tfrac{S_{3-i}}{B_{3-i}}\bar\delta_{3-i}\bigr)-\phi^2}+B_iY_i,$$
--   where
--   $$B_i=\frac{s_i(2(1+\phi)+\phi s_{3-i})}{4(1+\phi)^2-\phi^2s_1s_2}+\frac{2(1+\phi)S_i\bar\delta_i+\phi s_iS_{3-i}\bar\delta_{3-i}}{4(1+\phi)^2-\phi^2s_1s_2},$$
--   and its order rule is `eqOrder`. In particular the equilibrium exists and is unique, for each of the four sharing cases.
--
--   All later comparisons of profits rest on this characterization.
--
--   Differences from the source:
--   - correction: Assumption 1(b): E[Y1Y2|θ] = 0 → E[(Y1−θ)(Y2−θ)|θ] = 0; reason: the printed form gives E[Y1Y2] = 0, while the printed relations give E[Y1Y2] = E[Y2 E[θ|Y2]] = σ > 0, so with σ > 0 no model satisfies it; the corrected form is the one the normal-normal example of p.8 satisfies
--   - reading: E[Yi|Y3−i] = E[θ|Y3−i] is listed as implied by Assumption 1 (p.8) → it is a hypothesis of the signal model (field cross_forecast); reason: it needs E[Yi|θ,Y3−i] = θ, which conditional uncorrelatedness alone does not obviously give; it is exactly what the equilibrium uses, and no independence assumption is added
--   - encoding: t_i = 1/E[V(Y_i|θ)] → t_i = 1/E[(Y_i−θ)²]; reason: equal under Assumption 1(a)
--   - encoding: manufacturers 1, 2 and the index 3 − i → Fin 2 and the index 1 - i; reason: Lean indexing; same instances
--   - encoding: Π_i = max over w_i of w_i E[q_i*], given i's information → ex-ante optimality over measurable f with f∘Y_i in L²; reason: pointwise optimality at almost every signal is the same condition for this quadratic payoff
--   - encoding: the retailer's forecast E[θ|δ1,δ2] (p.10) → S1 X1 + S2 X2, with X_j = Y_j if shared and the signal inferred from w_j otherwise; reason: this is the p.8 formula for E[θ|Y1,Y2] at the known or inferred signals; assumption_1_relations proves it
--   - correction: q_i contains S2 δ1 Y2 and (S1/B1)δ̄1 + (S1/B1)δ̄1 → S2 δ2 Y2 and (S1/B1)δ̄1 + (S2/B2)δ̄2; reason: at δ = (0,1) the printed form drops the shared Y2 and at δ = (1,0) counts Y2 twice; the retailer's first-order condition gives the corrected form
--   - reading: "the equilibrium wholesale prices and order quantities are as follows" → an if and only if: existence and uniqueness among linear separating equilibria; reason: the paper treats the equilibrium as unique and restricts to linear separating equilibria (p.9)
-- source:
--   Jain, Sharing Demand Information with Retailer under Upstream Competition, SSRN:3388957 (PDF of 2021-04-25), Proposition 1, p.11

import Mathlib
import Definitions.Def_PushInfoShare_IsSignalModel
import Definitions.Def_PushInfoShare_accuracy
import Definitions.Def_PushInfoShare_IsLinearSeparatingEq
import Definitions.Def_PushInfoShare_eqIntercept
import Definitions.Def_PushInfoShare_eqOrder

open MeasureTheory

namespace PushInfoShare

/-- Proposition 1, Jain, SSRN:3388957 (PDF of 2021-04-25), p.11 (corrected order rule): for every
sharing decision `δ` and `φ ≥ 0`, a profile is a linear separating equilibrium if and only if its
price coefficients are `eqIntercept` and `eqSlope` and its order rule is `eqOrder`. So the
equilibrium exists and is unique, and it is the printed one.

**Formalization Note.** `eqOrder` corrects two index slips of the page. Existence and uniqueness
are read from "the equilibrium wholesale prices and order quantities are as follows". -/
theorem proposition_1 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {θ : Ω → ℝ} {Y : Fin 2 → Ω → ℝ} {σ : ℝ} (hM : IsSignalModel μ θ Y σ) {a φ : ℝ} (hφ : 0 ≤ φ)
    (δ : Fin 2 → Bool) (str : Profile) :
    IsLinearSeparatingEq μ θ Y σ a φ δ str ↔
      ∀ i : Fin 2,
        str.α i = eqIntercept (accuracy μ θ Y σ) (jointWeight μ θ Y σ) a φ δ i ∧
        str.B i = eqSlope (accuracy μ θ Y σ) (jointWeight μ θ Y σ) φ δ i ∧
        ∀ w y : Fin 2 → ℝ,
          str.q i w y = eqOrder (accuracy μ θ Y σ) (jointWeight μ θ Y σ) a φ δ i w y := by sorry

end PushInfoShare
