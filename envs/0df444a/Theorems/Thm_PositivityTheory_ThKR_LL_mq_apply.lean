-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_LL_mq_apply
-- name    : PositivityTheory.ThKR.LL.mq_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:33:29.55428+00:00
-- url     : https://prove2.me/theorems/4a8a1c7a-f353-48a2-9af6-cf2dcf485b00
-- title:
--   LL: mq apply
-- statement:
--   The LL construction uses the mq apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/NormExpSubLe.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/NormExpSubLe.lean#L15-L20

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_NormExpSubLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l]

theorem PositivityTheory.ThKR.LL.mq_apply (S : Eu l →L[ℝ] Eu l) (f : Sch l) (x : Eu l) : mq S f x = ((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I * f x := by sorry
