-- Prove2me | Theorems.Thm_PushInfoShare_proposition_5
-- name    : PushInfoShare.proposition_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:50:25.392998+00:00
-- url     : https://prove2.me/theorems/6d7f5e28-dd95-41e3-b462-10fa123eceb2
-- title:
--   Proposition 5, p.17 — substitutability thresholds for information sharing (corrected: thresholds exist exactly under $H_1,H_2,H_3$)
-- statement:
--   Let the two manufacturers have the same accuracy $s$, let $a>0$, and consider the equilibrium profits as functions of the substitution level $\phi\ge0$. Write
--   $$g_1=\Pi_i^{P_i}-\Pi_i^N,\qquad g_2=\Pi_i^F-\Pi_i^{P_{3-i}},\qquad g_3=\Pi_i^F-\Pi_i^N,\qquad \hat s=\frac{\sqrt{193}-9}{14}.$$
--   Say that $g$ *crosses down at* $\hat\phi$ if $\hat\phi>0$, $g>0$ on $[0,\hat\phi)$, $g(\hat\phi)=0$ and $g<0$ on $(\hat\phi,\infty)$. Then:
--
--   1. (a) If $H_1$ holds, $g_1$ crosses down at some $\hat\phi_1$; otherwise $g_1>0$ for all $\phi\ge0$.
--   2. (b) If $s\le\hat s$, then $g_2>0$ for all $\phi\ge0$. If $s>\hat s$ and $H_2$ holds, $g_2$ crosses down at some $\hat\phi_2$; if $s>\hat s$ and $H_2$ fails, $g_2>0$ for all $\phi\ge0$.
--   3. (c) If $H_3$ holds, $g_3$ crosses down at some $\hat\phi_3$; otherwise $g_3>0$ for all $\phi\ge0$.
--   4. (d) $\hat\phi_3<\hat\phi_1<\hat\phi_2$, a threshold that does not exist counting as $+\infty$: if $\hat\phi_1$ exists, then $\hat\phi_3$ exists and $\hat\phi_3<\hat\phi_1$; if $\hat\phi_2$ exists, then $\hat\phi_1$ exists and $\hat\phi_1<\hat\phi_2$.
--
--   The result says that a manufacturer's preference flips from sharing to withholding as competition intensifies, and it determines exactly for which $(a^2/\sigma,s)$ the flip occurs.
--
--   **Formalization Note** As printed, the clauses (a), (b) and (c) are false: $\hat s$ is a root of the $a^2$ part of the limit of $\phi g_2$, while the $\sigma$ part of profit has the same order in $1/\phi$. The conditions $H_1,H_2,H_3$ are written out in `condH1`, `condH2`, `condH3`.
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
--   - correction: (a), (c) "For each s, there exists φ̂" → the threshold exists exactly under H1, respectively H3; reason: the printed clauses fail at a² = 1/1000, σ = 1, s = 1/5, where both gaps are positive for all φ ≥ 0
--   - correction: (b) "when s > ŝ, there exists φ̂2" → for s > ŝ the threshold exists exactly under H2; reason: the printed clause fails at a = σ = 1, s = 2/5 > ŝ, where the gap is positive for all φ ≥ 0
--   - correction: "and Π < Π otherwise" → the strict sign for φ > φ̂ and equality at φ̂; reason: the gap is continuous and changes sign, so it is zero at the threshold
--   - reading: (d) φ̂3 < φ̂1 < φ̂2 → a missing threshold counts as +∞: if φ̂1 exists then φ̂3 exists and φ̂3 < φ̂1, and if φ̂2 exists then φ̂1 exists and φ̂1 < φ̂2; reason: p.19 treats φ̂2 as applicable only for s larger than ŝ, i.e. as +∞ otherwise, and this is the stronger of the two readings
--   - generalization: (b) "When s < ŝ", and nothing when no threshold exists → s ≤ ŝ, and ¬Hk implies the gap is positive for all φ ≥ 0; reason: these specialize to the source wherever the source is true
-- source:
--   Jain, Sharing Demand Information with Retailer under Upstream Competition, SSRN:3388957 (PDF of 2021-04-25), Proposition 5, p.17

import Mathlib
import Definitions.Def_PushInfoShare_IsSignalModel
import Definitions.Def_PushInfoShare_accuracy
import Definitions.Def_PushInfoShare_IsEquilibriumFamily
import Definitions.Def_PushInfoShare_onlyShares
import Definitions.Def_PushInfoShare_profitGap
import Definitions.Def_PushInfoShare_CrossesDown
import Definitions.Def_PushInfoShare_AlwaysPos
import Definitions.Def_PushInfoShare_condH1
import Definitions.Def_PushInfoShare_condH2
import Definitions.Def_PushInfoShare_condH3
import Definitions.Def_PushInfoShare_sHat

open MeasureTheory

namespace PushInfoShare

/-- Proposition 5, Jain, SSRN:3388957 (PDF of 2021-04-25), p.17, corrected. Let the manufacturers
have the same accuracy `s`, and write `g₁ = Πᵢ^{Pᵢ} − Πᵢᴺ`, `g₂ = Πᵢᶠ − Πᵢ^{P₃₋ᵢ}` and
`g₃ = Πᵢᶠ − Πᵢᴺ` as functions of `φ`. Then:

* (a) `g₁` has a downward crossing if `H1`, and is positive for all `φ ≥ 0` if not;
* (b) `g₂` is positive for all `φ ≥ 0` if `s ≤ ŝ`; if `s > ŝ`, it has a downward crossing if `H2`,
  and is positive for all `φ ≥ 0` if not;
* (c) `g₃` has a downward crossing if `H3`, and is positive for all `φ ≥ 0` if not;
* (d) `φ̂₃ < φ̂₁ < φ̂₂`, a threshold that does not exist counting as `+∞` (p.19): if `φ̂₁`
  exists then `φ̂₃` exists and `φ̂₃ < φ̂₁`; if `φ̂₂` exists then `φ̂₁` exists and `φ̂₁ < φ̂₂`.

**Formalization Note.** As printed, (a), (b) and (c) are false: `ŝ` comes from the `a²` part of
profit, and the `σ` part has the same order in `1/φ`. `H1`, `H2`, `H3` are the exact conditions on
`(a²/σ, s)`, and the printed strict sign "otherwise" fails at the threshold itself. The accuracy
`s` is in `(0, 1)` by `IsSignalModel`. -/
theorem proposition_5 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {θ : Ω → ℝ} {Y : Fin 2 → Ω → ℝ} {σ : ℝ} (hM : IsSignalModel μ θ Y σ) {a s : ℝ} (ha : 0 < a) (hs : ∀ i, accuracy μ θ Y σ i = s)
    {str : ℝ → (Fin 2 → Bool) → Profile} (hstr : IsEquilibriumFamily μ θ Y σ a str) (i : Fin 2) :
    (condH1 a σ s → ∃ φ₁,
      CrossesDown (profitGap μ Y str (onlyShares i) (fun _ => false) i) φ₁) ∧
    (¬ condH1 a σ s → AlwaysPos (profitGap μ Y str (onlyShares i) (fun _ => false) i)) ∧
    (s ≤ sHat → AlwaysPos (profitGap μ Y str (fun _ => true) (onlyShares (1 - i)) i)) ∧
    (sHat < s → condH2 a σ s → ∃ φ₂,
      CrossesDown (profitGap μ Y str (fun _ => true) (onlyShares (1 - i)) i) φ₂) ∧
    (sHat < s → ¬ condH2 a σ s →
      AlwaysPos (profitGap μ Y str (fun _ => true) (onlyShares (1 - i)) i)) ∧
    (condH3 a σ s → ∃ φ₃,
      CrossesDown (profitGap μ Y str (fun _ => true) (fun _ => false) i) φ₃) ∧
    (¬ condH3 a σ s → AlwaysPos (profitGap μ Y str (fun _ => true) (fun _ => false) i)) ∧
    (∀ φ₁, CrossesDown (profitGap μ Y str (onlyShares i) (fun _ => false) i) φ₁ →
      ∃ φ₃, CrossesDown (profitGap μ Y str (fun _ => true) (fun _ => false) i) φ₃ ∧ φ₃ < φ₁) ∧
    (∀ φ₂, CrossesDown (profitGap μ Y str (fun _ => true) (onlyShares (1 - i)) i) φ₂ →
      ∃ φ₁, CrossesDown (profitGap μ Y str (onlyShares i) (fun _ => false) i) φ₁ ∧ φ₁ < φ₂) := by sorry

end PushInfoShare
