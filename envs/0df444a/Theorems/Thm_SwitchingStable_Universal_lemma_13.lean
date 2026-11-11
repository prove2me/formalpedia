-- Prove2me | Theorems.Thm_SwitchingStable_Universal_lemma_13
-- name    : SwitchingStable.Universal.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:58:34.359606+00:00
-- url     : https://prove2.me/theorems/e32bfb1a-e0d1-4a31-a594-f135df4f131c
-- title:
--   Lemma 13 — Local directional costs and reserves
-- statement:
--   Fix a stable matching and either direction in the promoted market. With the required local cuts, the expected basic directional cost is at least $\alpha$ on $R_0$, $\eta$ on $R_1$, $\delta_2$ on $E\setminus E_{\rm adj}$, $\zeta$ on $E_{\rm adj}$, $\sigma$ on $S$, $\gamma$ on $W$, $\delta_2$ on $F_a$, and zero on $B$. In addition,
--   $$D:\ +\delta_2,\qquad D_0:\ +\delta_2+\lambda.$$
--   Every nonexceptional $C_0$ occurrence retains $F_1+F_2$ pointwise with expectation at least $\alpha+\delta_2$. The $F_a$ estimate is its elementary second-layer term. The full $D_0$ estimate is used as a type-zero cost. The reserve comparisons are
--   $$\chi>\delta_2+2\gamma+2\delta_4+\delta_5+3(\xi+\psi),\qquad\chi_{3,2}>\gamma+\delta_4+\delta_5+3\psi>0.$$
--   This retains all local estimates and both reserves.
--
--   Differences from the source:
--   - encoding: The required local witnesses, their basic costs and additional D and D0 costs → Explicit localCuts and fullLocalCost; the estimate holds under any further valid cuts; reason: Expands the complete class table and additive clauses and retains the selected elementary terms instead of making a scalar saving assumption.
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), p. 9, PDF p. 10, Lemma 13

import Mathlib
import Definitions.Def_SwitchingStable_Universal_Local

namespace SwitchingStable.Universal

open MeasureTheory

theorem lemma_13 {n : ℕ} (I : StableMatching.Instance n) (hI : StablePartnersFirst I)
    (μ : StableMatching.Matching n) (hμ : I.IsStable μ) (ε : Direction) (u : Fin n)
    (cuts : Finset (Cut n)) (hcuts : legalCuts I μ u ε cuts)
    (hlocal : localCuts I μ ε u ⊆ cuts) :
    MeasureTheory.Integrable (saving I μ u ε cuts) (revealLaw n) ∧
    fullLocalCost I μ ε u ≤ expected (saving I μ u ε cuts) ∧
    (C0 I μ ε u → ¬ Exceptional I μ ε u →
      let c1 := realCut 1 (next I μ ε (next I μ ε u))
      let c2 := if distance I μ u ε < 2 then endpointCut ε 2 else realCut 2 (chooseWitness I μ ε u 2)
      (∀ t, Good I μ u t → eventTerm I μ u ε c1 t + eventTerm I μ u ε c2 t ≤ saving I μ u ε cuts t) ∧
      alpha+delta 2 ≤ expected (fun t => eventTerm I μ u ε c1 t + eventTerm I μ u ε c2 t)) ∧
    (Fa I μ ε u → delta 2 ≤ expected (eventTerm I μ u ε (realCut 2 (chooseWitness I μ ε u 2)))) ∧
    delta 2 + 2*gamma + 2*delta 4 + delta 5 + 3*(xi+psi) < chi ∧
    gamma+delta 4+delta 5+3*psi < chi32 ∧ 0 < gamma+delta 4+delta 5+3*psi := by sorry

end SwitchingStable.Universal
