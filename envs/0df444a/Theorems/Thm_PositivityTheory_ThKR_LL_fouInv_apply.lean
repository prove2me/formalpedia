-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_LL_fouInv_apply
-- name    : PositivityTheory.ThKR.LL.fouInv_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:43.721079+00:00
-- url     : https://prove2.me/theorems/25097634-4892-48a4-b172-44342eaa6010
-- title:
--   LL: fou Inv apply
-- statement:
--   The LL construction uses the fou Inv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/IsoOfIntegral.lean#L135-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/IsoOfIntegral.lean#L135-L135

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

theorem PositivityTheory.ThKR.LL.fouInv_apply (f : Sch l) : fouInv l f = 𝓕⁻ f := by sorry
