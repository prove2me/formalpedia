-- Prove2me | Theorems.Thm_PushInfoShare_proposition_5c
-- name    : PushInfoShare.proposition_5c
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:51:20.392325+00:00
-- url     : https://prove2.me/theorems/60783fe0-b509-4cc0-97c3-340b2ddd5e45
-- title:
--   Proposition 5(c), p.17 — threshold $\hat\phi_3$ (corrected: exists exactly under $H_3$)
-- statement:
--   Let the manufacturers have the same accuracy $s$, and let $g_3(\phi)=\Pi_i^F(\phi)-\Pi_i^N(\phi)$.
--
--   1. If $H_3$ holds, there is $\hat\phi_3>0$ with $g_3>0$ on $[0,\hat\phi_3)$, $g_3(\hat\phi_3)=0$ and $g_3<0$ on $(\hat\phi_3,\infty)$.
--   2. If $H_3$ fails, $g_3>0$ for all $\phi\ge0$.
--
--   This compares the manufacturers' collective outcomes under full sharing and no sharing.
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
--   - correction: (c) "For each s, there exists φ̂3" → there is a downward crossing exactly under H3; reason: the printed clause fails at a² = 1/1000, σ = 1, s = 1/5, where the gap is positive for all φ ≥ 0
--   - correction: "and Π < Π otherwise" → the strict sign for φ > φ̂ and equality at φ̂; reason: the gap is continuous and changes sign, so it is zero at the threshold
--   - generalization: the source says nothing when no threshold exists → ¬H3 implies the gap is positive for all φ ≥ 0; reason: the two clauses agree with the source wherever the source is true
-- source:
--   Jain, Sharing Demand Information with Retailer under Upstream Competition, SSRN:3388957 (PDF of 2021-04-25), Proposition 5(c), p.17

import Mathlib
import Definitions.Def_PushInfoShare_IsSignalModel
import Definitions.Def_PushInfoShare_accuracy
import Definitions.Def_PushInfoShare_IsEquilibriumFamily
import Definitions.Def_PushInfoShare_onlyShares
import Definitions.Def_PushInfoShare_profitGap
import Definitions.Def_PushInfoShare_CrossesDown
import Definitions.Def_PushInfoShare_AlwaysPos
import Definitions.Def_PushInfoShare_condH3

open MeasureTheory

namespace PushInfoShare

/-- Proposition 5(c), Jain, SSRN:3388957 (PDF of 2021-04-25), p.17 (corrected): with equal accuracies
`s`, the gap `Πᵢᶠ − Πᵢᴺ` crosses zero downward at some `φ̂₃` if `H3` holds, and is positive at every
`φ ≥ 0` if `H3` fails.

**Formalization Note.** The printed clause, "for each s", is false for small `a²/σ`. `H3` is the
exact condition. -/
theorem proposition_5c {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {θ : Ω → ℝ} {Y : Fin 2 → Ω → ℝ} {σ : ℝ} (hM : IsSignalModel μ θ Y σ) {a s : ℝ} (ha : 0 < a) (hs : ∀ i, accuracy μ θ Y σ i = s)
    {str : ℝ → (Fin 2 → Bool) → Profile} (hstr : IsEquilibriumFamily μ θ Y σ a str) (i : Fin 2) :
    (condH3 a σ s → ∃ φ₃,
      CrossesDown (profitGap μ Y str (fun _ => true) (fun _ => false) i) φ₃) ∧
    (¬ condH3 a σ s → AlwaysPos (profitGap μ Y str (fun _ => true) (fun _ => false) i)) := by sorry

end PushInfoShare
