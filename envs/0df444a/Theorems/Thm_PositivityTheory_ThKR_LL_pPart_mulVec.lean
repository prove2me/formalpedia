-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_LL_pPart_mulVec
-- name    : PositivityTheory.ThKR.LL.pPart_mulVec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:46.173803+00:00
-- url     : https://prove2.me/theorems/d8385002-6fdc-4e96-bafd-f6a6cb85055a
-- title:
--   LL: p Part mul Vec
-- statement:
--   The LL construction uses the p Part mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalLift.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalLift.lean#L20-L23

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

theorem PositivityTheory.ThKR.LL.pPart_mulVec (g : Matrix (l ⊕ l) (l ⊕ l) ℝ) (w : l ⊕ l → ℝ) :
    pPart (g *ᵥ w) = bl Sum.inl Sum.inl g (pPart w) + bl Sum.inl Sum.inr g (qPart w) := by sorry
