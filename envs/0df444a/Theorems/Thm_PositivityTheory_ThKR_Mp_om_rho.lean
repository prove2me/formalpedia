-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Mp_om_rho
-- name    : PositivityTheory.ThKR.Mp.om_rho
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:22:42.246132+00:00
-- url     : https://prove2.me/theorems/cecff349-e78f-5f84-8c87-d80c38eaa005
-- title:
--   Mp: om rho
-- statement:
--   The Mp construction uses the om rho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/ContinuousPair.lean#L99-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/ContinuousPair.lean#L99-L99

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_LocalLift
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL
open scoped Real ContDiff
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable (l : Type) [Fintype l] [DecidableEq l]
variable {l}

theorem PositivityTheory.ThKR.Mp.om_rho (g : G l) (w : l ⊕ l → ℝ) (f : L2 l) : om g (rho w f) = rho ((pr g).1 *ᵥ w) (om g f) := by sorry
