-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Join_two_data
-- name    : PositivityTheory.ThKR.Join.two_data
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:55:01.558379+00:00
-- url     : https://prove2.me/theorems/88dea2e0-a05b-5b76-8a59-20e74739a1e5
-- title:
--   Join: two data
-- statement:
--   The Join construction uses the two data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalPoly.lean#L240-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalPoly.lean#L240-L250

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

theorem PositivityTheory.ThKR.Join.two_data (D : RealData) (h : D.Hyp) :
    Two D.P D.Q D.R D.S ((D.κ : ℂ) / 2) ∧ Two D.P' D.Q' D.R D.S (-((D.κ : ℂ) / 2)) := by sorry
