-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_LL_iso_of_integral
-- name    : PositivityTheory.ThKR.LL.iso_of_integral
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:59.821403+00:00
-- url     : https://prove2.me/theorems/16a42221-7fc5-4ab6-b491-0a09922e8b20
-- title:
--   LL: iso of integral
-- statement:
--   The LL construction uses the iso of integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/IsoOfIntegral.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/IsoOfIntegral.lean#L37-L40

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

theorem PositivityTheory.ThKR.LL.iso_of_integral {S : Sch l →L[ℂ] Sch l} (h : ∀ f : Sch l, ∫ x, ‖S f x‖ ^ (2 : ℝ) = ∫ x, ‖f x‖ ^ (2 : ℝ)) : Iso S := by sorry
