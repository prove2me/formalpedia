-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_LL_dil_apply
-- name    : PositivityTheory.ThKR.LL.dil_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:01.594838+00:00
-- url     : https://prove2.me/theorems/0efba170-6d33-4008-ab2e-1a03d30ad4c2
-- title:
--   LL: dil apply
-- statement:
--   The LL construction uses the dil apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/IsoOfIntegral.lean#L94-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/IsoOfIntegral.lean#L94-L96

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
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

theorem PositivityTheory.ThKR.LL.dil_apply {B : Eu l →L[ℝ] Eu l} (h : IsUnit B) (f : Sch l) (x : Eu l) : dil B f x = f (B x) := by sorry
