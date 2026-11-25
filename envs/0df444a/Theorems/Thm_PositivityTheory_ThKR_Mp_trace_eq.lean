-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Mp_trace_eq
-- name    : PositivityTheory.ThKR.Mp.trace_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:31:24.927829+00:00
-- url     : https://prove2.me/theorems/7adc0be2-b68f-4a05-8aea-76741000f216
-- title:
--   Mp: trace eq
-- statement:
--   The Mp construction uses the trace eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MetaplecticUnipotentBlockSecondDiag.lean#L256-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/MetaplecticUnipotentBlockSecondDiag.lean#L256-L271

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MetaplecticUnipotentBlockSecondDiag
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

theorem PositivityTheory.ThKR.Mp.trace_eq {P Q : Matrix l l ℂ} (hP : P.det ≠ 0) (S M : Matrix l l ℂ) (c : ℂ)
    (h : ∀ j k, ∑ a, P a j * M a k = c * Q k j) : ∑ j, ∑ k, S j k * M j k = c * (P⁻¹ * (S * Q)).trace := by sorry
