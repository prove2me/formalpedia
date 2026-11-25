-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_LL_isUnit_dil
-- name    : PositivityTheory.ThKR.LL.isUnit_dil
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:06:17.625914+00:00
-- url     : https://prove2.me/theorems/7442b93c-3ae4-4291-b21b-f9cbdcdf3ee3
-- title:
--   LL: is Unit dil
-- statement:
--   The LL construction uses the is Unit dil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/IsoOfIntegral.lean#L106-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/IsoOfIntegral.lean#L106-L109

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

theorem PositivityTheory.ThKR.LL.isUnit_dil {B : Eu l →L[ℝ] Eu l} (h : IsUnit B) : IsUnit (dil B) := by sorry
