-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_LL_qPart_mulVec
-- name    : PositivityTheory.ThKR.LL.qPart_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:15.586652+00:00
-- url     : https://prove2.me/theorems/8c30c7e9-881d-4f5b-b78d-59e9dca1a83d
-- title:
--   LL: q Part mul Vec
-- statement:
--   The LL construction uses the q Part mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalLift.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalLift.lean#L25-L28

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

theorem PositivityTheory.ThKR.LL.qPart_mulVec (g : Matrix (l ⊕ l) (l ⊕ l) ℝ) (w : l ⊕ l → ℝ) :
    qPart (g *ᵥ w) = bl Sum.inr Sum.inl g (pPart w) + bl Sum.inr Sum.inr g (qPart w) := by sorry
