-- Prove2me | Theorems.Thm_SwitchingStable_Universal_lemma_12
-- name    : SwitchingStable.Universal.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:36.219876+00:00
-- url     : https://prove2.me/theorems/fe1f11b3-388b-4fe7-9d72-772bf6c04b0a
-- title:
--   Lemma 12 — Elementary witness event costs
-- statement:
--   Fix a stable matching, a coordinate and direction, and a valid additional witness at layer $1\le k\le5$, distinct from its coordinate and the first $k$ canonical owners. Fresh auxiliary witnesses are also permitted when an endpoint already supplies the cap. For the elementary event term $F_k$,
--   $$S_{\rm dir}\ge F_k,\qquad\mathbb E[F_k]\ge\delta_k.$$
--   The statement permits any further valid cuts and establishes integrability. Consequently the Section 3 selected witnesses on $R,E,W$ have the costs $\alpha,\delta_2,\gamma$, respectively. No independence of opposite-side witnesses is imposed.
--
--   Differences from the source:
--   - encoding: Pointwise elementary events on the infinite Bernoulli extensions and their expectations → The exact independent-priority product experiment, with pointwise assertions on successful runs and integrability as a conclusion; reason: Infinite unsuccessful runs are null; elementary auxiliary witnesses are distinct from every position mark used in the calculation.
--   - generalization: The Section 4 standing setting is the promoted market I-star → Any complete strict market, with the stated stable matching and valid elementary cuts; reason: The probability argument uses only distinct canonical owners, valid unchanged-edge implications and the product priority law; taking I to be the promoted market gives every source instance.
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), p. 8, PDF p. 9, Lemma 12

import Mathlib
import Definitions.Def_SwitchingStable_Universal_Transport

namespace SwitchingStable.Universal

open MeasureTheory

theorem lemma_12 {n : ℕ} (I : StableMatching.Instance n)
    (μ : StableMatching.Matching n) (hμ : I.IsStable μ) (u : Fin n) (ε : Direction)
    (c : Cut n) (hc : Elementary I μ u ε c) (hk : c.layer ≤ 5)
    (cuts : Finset (Cut n)) (hcuts : legalCuts I μ u ε cuts) (hmem : c ∈ cuts) :
    (∀ t, Good I μ u t → eventTerm I μ u ε c t ≤ saving I μ u ε cuts t) ∧
    MeasureTheory.Integrable (eventTerm I μ u ε c) (revealLaw n) ∧
    MeasureTheory.Integrable (saving I μ u ε cuts) (revealLaw n) ∧
    delta c.layer ≤ expected (eventTerm I μ u ε c) := by sorry

end SwitchingStable.Universal
