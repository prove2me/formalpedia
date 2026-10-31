-- Prove2me | Theorems.Thm_PushInfoShare_proposition_6a
-- name    : PushInfoShare.proposition_6a
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:49:03.064583+00:00
-- url     : https://prove2.me/theorems/fc02a8c2-acdd-4cd3-8038-1d512b4c37a9
-- title:
--   Proposition 6(a), p.20 — a manufacturer gains when its rival withholds (corrected: strict for $\phi>0$)
-- statement:
--   For $\phi>0$ and any accuracies $s_1,s_2$, whatever manufacturer $i$ does itself, it earns more when the rival does not share:
--   $$\Pi_i^{P_i}>\Pi_i^F,\qquad \Pi_i^N>\Pi_i^{P_{3-i}}.$$
--   This is the indirect signaling effect: the rival's inflated price shifts orders toward manufacturer $i$.
--
--   Differences from the source:
--   - correction: Assumption 1(b): E[Y1Y2|θ] = 0 → E[(Y1−θ)(Y2−θ)|θ] = 0; reason: the printed form gives E[Y1Y2] = 0, while the printed relations give E[Y1Y2] = E[Y2 E[θ|Y2]] = σ > 0, so with σ > 0 no model satisfies it; the corrected form is the one the normal-normal example of p.8 satisfies
--   - reading: E[Yi|Y3−i] = E[θ|Y3−i] is listed as implied by Assumption 1 (p.8) → it is a hypothesis of the signal model (field cross_forecast); reason: it needs E[Yi|θ,Y3−i] = θ, which conditional uncorrelatedness alone does not obviously give; it is exactly what the equilibrium uses, and no independence assumption is added
--   - reading: a is "the average level of demand" (p.7), with no sign stated → 0 < a; reason: the reading of a mean demand level; the paper never writes the sign
--   - encoding: t_i = 1/E[V(Y_i|θ)] → t_i = 1/E[(Y_i−θ)²]; reason: equal under Assumption 1(a)
--   - encoding: manufacturers 1, 2 and the index 3 − i → Fin 2 and the index 1 - i; reason: Lean indexing; same instances
--   - encoding: Π_i = max over w_i of w_i E[q_i*], given i's information → ex-ante optimality over measurable f with f∘Y_i in L²; reason: pointwise optimality at almost every signal is the same condition for this quadratic payoff
--   - encoding: the retailer's forecast E[θ|δ1,δ2] (p.10) → S1 X1 + S2 X2, with X_j = Y_j if shared and the signal inferred from w_j otherwise; reason: this is the p.8 formula for E[θ|Y1,Y2] at the known or inferred signals; assumption_1_relations proves it
--   - correction: Proposition 6(a) with no restriction on φ → 0 < φ; reason: at φ = 0 neither manufacturer's coefficients depend on the other's decision, so both inequalities are equalities
-- source:
--   Jain, Sharing Demand Information with Retailer under Upstream Competition, SSRN:3388957 (PDF of 2021-04-25), Proposition 6(a), p.20

import Mathlib
import Definitions.Def_PushInfoShare_IsSignalModel
import Definitions.Def_PushInfoShare_IsLinearSeparatingEq
import Definitions.Def_PushInfoShare_onlyShares
import Definitions.Def_PushInfoShare_profit

open MeasureTheory

namespace PushInfoShare

/-- Proposition 6(a), Jain, SSRN:3388957 (PDF of 2021-04-25), p.20 (corrected: strict for `φ > 0`):
`Πᵢ^{Pᵢ} > Πᵢᶠ` and `Πᵢᴺ > Πᵢ^{P₃₋ᵢ}`, whatever the two accuracies.

**Formalization Note.** At `φ = 0` neither manufacturer's coefficients depend on the other's
decision, so both inequalities are equalities there. -/
theorem proposition_6a {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {θ : Ω → ℝ} {Y : Fin 2 → Ω → ℝ} {σ : ℝ} (hM : IsSignalModel μ θ Y σ) {a φ : ℝ} (ha : 0 < a) (hφ : 0 < φ) (i : Fin 2)
    {strPi strF strN strPj : Profile}
    (hPi : IsLinearSeparatingEq μ θ Y σ a φ (onlyShares i) strPi)
    (hF : IsLinearSeparatingEq μ θ Y σ a φ (fun _ => true) strF)
    (hN : IsLinearSeparatingEq μ θ Y σ a φ (fun _ => false) strN)
    (hPj : IsLinearSeparatingEq μ θ Y σ a φ (onlyShares (1 - i)) strPj) :
    profit μ Y strF i < profit μ Y strPi i ∧ profit μ Y strPj i < profit μ Y strN i := by sorry

end PushInfoShare
