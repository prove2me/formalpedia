-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Join_two_of
-- name    : PositivityTheory.ThKR.Join.two_of
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:58:48.394624+00:00
-- url     : https://prove2.me/theorems/a39a4286-775d-55d5-a84a-aac6941b597a
-- title:
--   Join: two of
-- statement:
--   The Join construction uses the two of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalPoly.lean#L187-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalPoly.lean#L187-L238

import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_ExistsGreatestProperInvariantSubmoduleOfSide
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_LocalPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Join
open PositivityTheory.KReal PositivityTheory.ThKF.Unit

theorem PositivityTheory.ThKR.Join.two_of {p q r s : ℕ} {c : ℂ} (τ : ℚ) {La : Ix r s → ℚ} (h : Side La (ThC p q r s c) (thAct p q r s c τ)) :
    Two p q r s c := by sorry
