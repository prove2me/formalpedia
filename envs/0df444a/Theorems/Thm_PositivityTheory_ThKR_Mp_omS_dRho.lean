-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Mp_omS_dRho
-- name    : PositivityTheory.ThKR.Mp.omS_dRho
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:02:27.233468+00:00
-- url     : https://prove2.me/theorems/7fa9a969-7859-458f-9ce1-4f822468dea9
-- title:
--   Mp: om S d Rho
-- statement:
--   The Mp construction uses the om S d Rho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/ContinuousPair.lean#L101-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/ContinuousPair.lean#L101-L102

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_LocalLift
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Theorems.Thm_GlobalTheory_RealWeil_omS_dRho
import Theorems.Thm_PositivityTheory_ThKF_E_Impl_dRho

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

theorem PositivityTheory.ThKR.Mp.omS_dRho (g : G l) (w : l ⊕ l → ℝ) (f : Sch l) : omS g (dRho w f) = dRho ((pr g).1 *ᵥ w) (omS g f) := by sorry
