-- Prove2me | Theorems.Thm_SwitchingStable_Universal_lemma_15
-- name    : SwitchingStable.Universal.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:58:20.834203+00:00
-- url     : https://prove2.me/theorems/597418e9-4791-40e4-a66b-05240ec40667
-- title:
--   Lemma 15 — Mixed types and residual savings
-- statement:
--   At a coordinate choose a type and depth for each direction. For nonzero type $i\in\{1,2,3\}$ and depth $r\in\{1,2,3\}$, select the consecutive elementary layers, with cost $\sum_{a=0}^{r-1}\delta_{i+a}$ and weight $\omega_i-p(r)$, where $p(1)=\xi+\psi$, $p(2)=\psi$, $p(3)=0$. Type zero uses any established full directional cost and weight $-\omega_1$. Then
--   $$\mathbb E[S]\ge\operatorname{cost}_R+\operatorname{cost}_L+\operatorname{weight}_R+\operatorname{weight}_L+\mathbb E[R_R]+\mathbb E[R_L].$$
--   For a nonzero direction its residual is its actual directional saving minus its actual selected terms. The residual is nonnegative and integrable. Surplus of selected expectations over the $\delta$ bounds is already used by the interaction estimate and is not counted again.
--
--   Differences from the source:
--   - reading: The residual clause follows the nonzero-type selected terms and the separate type-zero full-cost convention → Residual equals the actual directional difference for nonzero types and zero for a full-cost type-zero direction; reason: The paragraph before Lemma 15 and its Appendix D proof consume a full directional estimate for type zero; residuals after selected F terms apply to nonzero types, so that full estimate is not spent twice.
--   - generalization: The Section 4 standing setting is the promoted market I-star → Any complete strict market, with the stated stable matching and valid elementary cuts; reason: The probability argument uses only distinct canonical owners, valid unchanged-edge implications and the product priority law; taking I to be the promoted market gives every source instance.
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), p. 9, PDF p. 10, Lemma 15

import Mathlib
import Definitions.Def_SwitchingStable_Universal_Local

namespace SwitchingStable.Universal

open MeasureTheory

theorem lemma_15 {n : ℕ} (I : StableMatching.Instance n)
    (μ : StableMatching.Matching n) (hμ : I.IsStable μ) (u : Fin n)
    (r l : LayerChoice n) (hr : r.Valid I μ u .right) (hl : l.Valid I μ u .left) :
    MeasureTheory.Integrable (r.residual I μ u .right) (revealLaw n) ∧
    MeasureTheory.Integrable (l.residual I μ u .left) (revealLaw n) ∧
    (∀ t, Good I μ u t → 0 ≤ r.residual I μ u .right t ∧ 0 ≤ l.residual I μ u .left t) ∧
    r.cost+l.cost+r.weight+l.weight +
      expected (r.residual I μ u .right) + expected (l.residual I μ u .left) ≤
      expected (jointSaving I μ u r.cuts l.cuts) := by sorry

end SwitchingStable.Universal
