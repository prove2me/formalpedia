-- Prove2me | Theorems.Thm_SwitchingStable_Universal_lemma_14
-- name    : SwitchingStable.Universal.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:58:23.361217+00:00
-- url     : https://prove2.me/theorems/065f480f-0f36-4ea5-a8f0-5817571e08ff
-- title:
--   Lemma 14 — Dependent-witness joint layered savings
-- statement:
--   Fix a stable matching and coordinate. Select finite layer sets $K_R,K_L\subseteq\{1,2,3,4,5\}$ and valid elementary witnesses on each side, permitting reused witnesses and fresh auxiliary endpoint witnesses. Distinct layer indices give pointwise bounds $S_R\ge\sum F_i^R$ and $S_L\ge\sum F_j^L$. With $J=S-S_R-S_L$,
--   $$\mathbb E\left[\sum_{i\in K_R}F_i^R+\sum_{j\in K_L}F_j^L+J\right]\ge\sum_{i\in K_R}\delta_i+\sum_{j\in K_L}\delta_j+\sum_{i\in K_R}\sum_{j\in K_L}e_{i+j}.$$
--   The estimate allows any additional valid cuts. Its pointwise conclusions also retain $J\ge0$ and the final support relation $X_u\le(A+B-1)e^{-S}$. This applies to dependent or incompatible reveal events.
--
--   Differences from the source:
--   - encoding: Finite layer sets with one selected witness for each layer and any further cuts → Finite cut sets whose layer projection is injective; integrability and the support relation are conclusions; reason: This is an equivalent indexed representation; the support relation is the displayed proof component of Theorem 1 on printed page 12.
--   - generalization: The Section 4 standing setting is the promoted market I-star → Any complete strict market, with the stated stable matching and valid elementary cuts; reason: The probability argument uses only distinct canonical owners, valid unchanged-edge implications and the product priority law; taking I to be the promoted market gives every source instance.
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), p. 9, PDF p. 10, Lemma 14

import Mathlib
import Definitions.Def_SwitchingStable_Universal_Local

namespace SwitchingStable.Universal

open MeasureTheory

theorem lemma_14 {n : ℕ} (I : StableMatching.Instance n)
    (μ : StableMatching.Matching n) (hμ : I.IsStable μ) (u : Fin n)
    (rs ls right left : Finset (Cut n))
    (hr : ∀ c ∈ rs, Elementary I μ u .right c ∧ c.layer ≤ 5)
    (hl : ∀ c ∈ ls, Elementary I μ u .left c ∧ c.layer ≤ 5)
    (hir : Set.InjOn Cut.layer (rs : Set (Cut n)))
    (hil : Set.InjOn Cut.layer (ls : Set (Cut n)))
    (hrr : rs ⊆ right) (hll : ls ⊆ left)
    (hR : legalCuts I μ u .right right) (hL : legalCuts I μ u .left left) :
    (∀ t, Good I μ u t →
      layerSum I μ u .right rs t ≤ saving I μ u .right right t ∧
      layerSum I μ u .left ls t ≤ saving I μ u .left left t ∧ 0 ≤ interaction I μ u right left t ∧
      (supportSize I μ u (predecessors u t) : ℝ) ≤
        ((firstMark I μ u .right t : ℝ)+firstMark I μ u .left t-1) *
          Real.exp (-jointSaving I μ u right left t)) ∧
    MeasureTheory.Integrable (fun t => layerSum I μ u .right rs t + layerSum I μ u .left ls t +
      interaction I μ u right left t) (revealLaw n) ∧
    (∑ c ∈ rs, delta c.layer) + (∑ c ∈ ls, delta c.layer) +
      (∑ c ∈ rs, ∑ d ∈ ls, e (c.layer+d.layer)) ≤
      expected (fun t => layerSum I μ u .right rs t + layerSum I μ u .left ls t + interaction I μ u right left t) := by sorry

end SwitchingStable.Universal
