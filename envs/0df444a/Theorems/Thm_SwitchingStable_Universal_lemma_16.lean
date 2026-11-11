-- Prove2me | Theorems.Thm_SwitchingStable_Universal_lemma_16
-- name    : SwitchingStable.Universal.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:58:42.243278+00:00
-- url     : https://prove2.me/theorems/fc64d246-670c-4840-9537-80eee2ac6d1c
-- title:
--   Lemma 16 — Tail second-layer saving
-- statement:
--   Fix a tail occurrence $u\in T_0$ of a stable matching in the promoted market, in either direction. Retain its original first-boundary witness $h=f^2(u)$. At most one additional supplier at distance at most two is needed. The explicit second-row term $H=F_2$ satisfies
--   $$S_{\rm dir}\ge F_1+H,\qquad H\ge0,\qquad\mathbb E[H]\ge\delta_2,\qquad\mathbb E[S_{\rm dir}]\ge\alpha+\delta_2.$$
--   The same supplier is reused when it already supplies row two; a fresh auxiliary endpoint witness is used only when the finite endpoint supplies that row. This keeps the first witness and supplies the second row without assuming the saving.
--
--   Differences from the source:
--   - encoding: There exists at most one extra witness and a nonnegative H, with the F2 construction given in Appendix D → The fixed-order secondCut and H equal to its elementary second-row event term; reason: This names the source construction explicitly; repeated suppliers and endpoint auxiliaries introduce no extra agent or constraint.
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), p. 10, PDF p. 11, Lemma 16

import Mathlib
import Definitions.Def_SwitchingStable_Universal_Local

namespace SwitchingStable.Universal

open MeasureTheory

theorem lemma_16 {n : ℕ} (I : StableMatching.Instance n) (hI : StablePartnersFirst I)
    (μ : StableMatching.Matching n) (hμ : I.IsStable μ) (u : Fin n) (ε : Direction) (hu : T0 I μ ε u) :
    let c1 := realCut 1 (next I μ ε (next I μ ε u))
    let c2 := secondCut I μ ε u
    Elementary I μ u ε c1 ∧ Elementary I μ u ε c2 ∧ c2.layer = 2 ∧
    legalCuts I μ u ε {c1,c2} ∧
    (∀ t, 0 ≤ eventTerm I μ u ε c2 t) ∧
    MeasureTheory.Integrable (eventTerm I μ u ε c2) (revealLaw n) ∧
    (∀ t, Good I μ u t → eventTerm I μ u ε c1 t+eventTerm I μ u ε c2 t ≤ saving I μ u ε {c1,c2} t) ∧
    delta 2 ≤ expected (eventTerm I μ u ε c2) ∧
    alpha+delta 2 ≤ expected (saving I μ u ε {c1,c2}) := by sorry

end SwitchingStable.Universal
