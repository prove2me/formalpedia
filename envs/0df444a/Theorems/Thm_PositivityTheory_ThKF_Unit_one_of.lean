-- Prove2me | Theorems.Thm_PositivityTheory_ThKF_Unit_one_of
-- name    : PositivityTheory.ThKF.Unit.one_of
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:40:46.646648+00:00
-- url     : https://prove2.me/theorems/09f09c98-d82f-5048-a5a4-8580da90b6b4
-- title:
--   Unit: one of
-- statement:
--   The Unit construction uses the one of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/ExistsGreatestProperInvariantSubmoduleOfSide.lean#L161-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/ExistsGreatestProperInvariantSubmoduleOfSide.lean#L161-L212

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLM
import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_ExistsGreatestProperInvariantSubmoduleOfSide
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
open PositivityTheory PositivityTheory.ThKF PositivityTheory.ThKF.Unit
open PositivityTheory.KReal

theorem PositivityTheory.ThKF.Unit.one_of {p q r s : ℕ} {c : ℂ} (τ : ℚ) {La : Ix r s → ℚ} (h : Side La (ThC p q r s c) (thAct p q r s c τ)) :
    One p q r s c := by sorry
