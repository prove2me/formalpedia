-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_LL_temperate_quad
-- name    : PositivityTheory.ThKR.LL.temperate_quad
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:18.800858+00:00
-- url     : https://prove2.me/theorems/adcef0fb-e818-4143-8cd3-e38ba09030e5
-- title:
--   LL: temperate quad
-- statement:
--   The LL construction uses the temperate quad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/IsoOfIntegral.lean#L42-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/IsoOfIntegral.lean#L42-L43

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

theorem PositivityTheory.ThKR.LL.temperate_quad (S : Eu l →L[ℝ] Eu l) : Function.HasTemperateGrowth fun x : Eu l => ⟪x, S x⟫ := by sorry
