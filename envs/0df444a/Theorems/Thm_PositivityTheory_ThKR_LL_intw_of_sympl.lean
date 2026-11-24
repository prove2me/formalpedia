-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_LL_intw_of_sympl
-- name    : PositivityTheory.ThKR.LL.intw_of_sympl
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:21.947502+00:00
-- url     : https://prove2.me/theorems/4d103372-33e0-4a0c-8bc7-b8c52b8353fb
-- title:
--   LL: intw of sympl
-- statement:
--   The LL construction uses the intw of sympl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalLift.lean#L71-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalLift.lean#L71-L87

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_NormExpSubLe
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_LocalLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l] [DecidableEq l]

theorem PositivityTheory.ThKR.LL.intw_of_sympl {g : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hg : ∀ w w', sympl (g *ᵥ w) (g *ᵥ w') = sympl w w')
    (h : IsUnit (bl Sum.inl Sum.inl g)) (c : ℝ) (w : l ⊕ l → ℝ) :
    Intw (big (Ring.inverse (bl Sum.inl Sum.inl g)) (bl Sum.inl Sum.inr g) (bl Sum.inr Sum.inl g) c) (pPart w) (qPart w)
      (pPart (g *ᵥ w)) (qPart (g *ᵥ w)) := by sorry
