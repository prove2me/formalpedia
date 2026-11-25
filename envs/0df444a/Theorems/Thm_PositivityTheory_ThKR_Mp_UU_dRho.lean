-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Mp_UU_dRho
-- name    : PositivityTheory.ThKR.Mp.UU_dRho
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:30:02.660742+00:00
-- url     : https://prove2.me/theorems/006f780a-2d9e-57ca-8d4e-c2fad4148275
-- title:
--   Mp: UU d Rho
-- statement:
--   The Mp construction uses the UU d Rho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MetaplecticUnipotentBlockSecondDiag.lean#L159-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MetaplecticUnipotentBlockSecondDiag.lean#L159-L164

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MetaplecticUnipotentBlockSecondDiag
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
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]

theorem PositivityTheory.ThKR.Mp.UU_dRho {S : Matrix l l ℝ} (hS : S.IsSymm) (t : ℝ) (w : l ⊕ l → ℝ) (f : Sch l) :
    UU S t (dRho w f) = dRho (nn S t *ᵥ w) (UU S t f) := by sorry
