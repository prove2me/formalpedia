-- Prove2me | Theorems.Thm_PushInfoShare_proposition_5b
-- name    : PushInfoShare.proposition_5b
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:52:04.993961+00:00
-- url     : https://prove2.me/theorems/4bea658f-4b2b-4985-a3fe-4d3c3bc1fa37
-- title:
--   Proposition 5(b), p.17 — threshold $\hat\phi_2$ (corrected: for $s>\hat s$ exists exactly under $H_2$)
-- statement:
--   Let the manufacturers have the same accuracy $s$, and let $g_2(\phi)=\Pi_i^F(\phi)-\Pi_i^{P_{3-i}}(\phi)$, with $\hat s=(\sqrt{193}-9)/14$.
--
--   1. If $s\le\hat s$, then $g_2>0$ for all $\phi\ge0$.
--   2. If $s>\hat s$ and $H_2$ holds, there is $\hat\phi_2>0$ with $g_2>0$ on $[0,\hat\phi_2)$, $g_2(\hat\phi_2)=0$ and $g_2<0$ on $(\hat\phi_2,\infty)$.
--   3. If $s>\hat s$ and $H_2$ fails, then $g_2>0$ for all $\phi\ge0$.
--
--   This is a manufacturer's incentive to share when its rival shares.
--
--   Differences from the source:
--   - correction: Assumption 1(b): E[Y1Y2|θ] = 0 → E[(Y1−θ)(Y2−θ)|θ] = 0; reason: the printed form gives E[Y1Y2] = 0, while the printed relations give E[Y1Y2] = E[Y2 E[θ|Y2]] = σ > 0, so with σ > 0 no model satisfies it; the corrected form is the one the normal-normal example of p.8 satisfies
--   - reading: E[Yi|Y3−i] = E[θ|Y3−i] is listed as implied by Assumption 1 (p.8) → it is a hypothesis of the signal model (field cross_forecast); reason: it needs E[Yi|θ,Y3−i] = θ, which conditional uncorrelatedness alone does not obviously give; it is exactly what the equilibrium uses, and no independence assumption is added
--   - reading: a is "the average level of demand" (p.7), with no sign stated → 0 < a; reason: the reading of a mean demand level; the paper never writes the sign
--   - encoding: t_i = 1/E[V(Y_i|θ)] → t_i = 1/E[(Y_i−θ)²]; reason: equal under Assumption 1(a)
--   - encoding: manufacturers 1, 2 and the index 3 − i → Fin 2 and the index 1 - i; reason: Lean indexing; same instances
--   - encoding: Π_i = max over w_i of w_i E[q_i*], given i's information → ex-ante optimality over measurable f with f∘Y_i in L²; reason: pointwise optimality at almost every signal is the same condition for this quadratic payoff
--   - encoding: the retailer's forecast E[θ|δ1,δ2] (p.10) → S1 X1 + S2 X2, with X_j = Y_j if shared and the signal inferred from w_j otherwise; reason: this is the p.8 formula for E[θ|Y1,Y2] at the known or inferred signals; assumption_1_relations proves it
--   - encoding: Π_i^F, Π_i^N, Π_i^{P_i}, Π_i^{P_{3−i}} denote the equilibrium profits → profits along any family of equilibria indexed by φ ≥ 0 and the sharing decision; reason: Proposition 1 makes each equilibrium unique, so the family is unique
--   - correction: (b) "when s > ŝ, there exists φ̂2" → for s > ŝ there is a downward crossing exactly under H2; reason: the printed clause fails at a = σ = 1, s = 2/5 > ŝ, where the gap is positive for all φ ≥ 0
--   - correction: "and Π < Π otherwise" → the strict sign for φ > φ̂ and equality at φ̂; reason: the gap is continuous and changes sign, so it is zero at the threshold
--   - generalization: "When s < ŝ", and nothing when no threshold exists → s ≤ ŝ, and ¬H2 implies the gap is positive for all φ ≥ 0; reason: these specialize to the source wherever the source is true
-- source:
--   Jain, Sharing Demand Information with Retailer under Upstream Competition, SSRN:3388957 (PDF of 2021-04-25), Proposition 5(b), p.17

import Mathlib
import Definitions.Def_PushInfoShare_IsSignalModel
import Definitions.Def_PushInfoShare_accuracy
import Definitions.Def_PushInfoShare_IsEquilibriumFamily
import Definitions.Def_PushInfoShare_onlyShares
import Definitions.Def_PushInfoShare_profitGap
import Definitions.Def_PushInfoShare_CrossesDown
import Definitions.Def_PushInfoShare_AlwaysPos
import Definitions.Def_PushInfoShare_condH2
import Definitions.Def_PushInfoShare_sHat

open MeasureTheory

namespace PushInfoShare

/-- Proposition 5(b), Jain, SSRN:3388957 (PDF of 2021-04-25), p.17 (corrected): with equal accuracies
`s`, the gap `Πᵢᶠ − Πᵢ^{P₃₋ᵢ}` is positive at every `φ ≥ 0` if `s ≤ ŝ`; if `s > ŝ` it crosses zero
downward at some `φ̂₂` when `H2` holds and is positive at every `φ ≥ 0` when `H2` fails.

**Formalization Note.** The printed clause "when s > ŝ, there exists φ̂₂" is false without `H2`,
for instance at `a = σ = 1`, `s = 2/5`. -/
theorem proposition_5b {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {θ : Ω → ℝ} {Y : Fin 2 → Ω → ℝ} {σ : ℝ} (hM : IsSignalModel μ θ Y σ) {a s : ℝ} (ha : 0 < a) (hs : ∀ i, accuracy μ θ Y σ i = s)
    {str : ℝ → (Fin 2 → Bool) → Profile} (hstr : IsEquilibriumFamily μ θ Y σ a str) (i : Fin 2) :
    (s ≤ sHat → AlwaysPos (profitGap μ Y str (fun _ => true) (onlyShares (1 - i)) i)) ∧
    (sHat < s → condH2 a σ s → ∃ φ₂,
      CrossesDown (profitGap μ Y str (fun _ => true) (onlyShares (1 - i)) i) φ₂) ∧
    (sHat < s → ¬ condH2 a σ s →
      AlwaysPos (profitGap μ Y str (fun _ => true) (onlyShares (1 - i)) i)) := by sorry

end PushInfoShare
