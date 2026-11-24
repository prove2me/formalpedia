-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_LL_vf_apply
-- name    : PositivityTheory.ThKR.LL.vf_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:10.8704+00:00
-- url     : https://prove2.me/theorems/627f093b-ba84-40ff-b1ea-2f7b9f4fecff
-- title:
--   LL: vf apply
-- statement:
--   The LL construction uses the vf apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/NormExpSubLe.lean#L68-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/NormExpSubLe.lean#L68-L68

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

theorem PositivityTheory.ThKR.LL.vf_apply (H : Eu l →L[ℝ] Eu l) (f : Sch l) (x : Eu l) : vf H f x = fderiv ℝ f x (H x) := by sorry
