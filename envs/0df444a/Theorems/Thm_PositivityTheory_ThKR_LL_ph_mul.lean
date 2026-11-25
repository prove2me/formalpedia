-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_LL_ph_mul
-- name    : PositivityTheory.ThKR.LL.ph_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:07:43.433529+00:00
-- url     : https://prove2.me/theorems/db842731-fb45-5b9d-a378-34d5a6d51370
-- title:
--   LL: ph mul
-- statement:
--   The LL construction uses the ph mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/IsoOfIntegral.lean#L61-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/IsoOfIntegral.lean#L61-L67

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

theorem PositivityTheory.ThKR.LL.ph_mul (S T : Eu l →L[ℝ] Eu l) : ph S * ph T = ph (S + T) := by sorry
