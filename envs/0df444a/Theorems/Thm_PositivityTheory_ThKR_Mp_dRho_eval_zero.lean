-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Mp_dRho_eval_zero
-- name    : PositivityTheory.ThKR.Mp.dRho_eval_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:30:29.988809+00:00
-- url     : https://prove2.me/theorems/59c4dd06-a1a4-4a31-9cb4-e557b080c7a7
-- title:
--   Mp: d Rho eval zero
-- statement:
--   The Mp construction uses the d Rho eval zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MetaplecticUnipotentBlockSecondDiag.lean#L230-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MetaplecticUnipotentBlockSecondDiag.lean#L230-L233

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

theorem PositivityTheory.ThKR.Mp.dRho_eval_zero (w : l ⊕ l → ℝ) (h : Sch l) :
    dRho w h 0 = ∑ a, (w (.inl a) : ℂ) * (∂_{(EuclideanSpace.single a 1 : Eu l)} h) 0 := by sorry
