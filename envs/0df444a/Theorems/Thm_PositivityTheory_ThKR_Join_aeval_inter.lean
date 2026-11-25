-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Join_aeval_inter
-- name    : PositivityTheory.ThKR.Join.aeval_inter
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:08:45.028018+00:00
-- url     : https://prove2.me/theorems/cfcdffdd-c342-4bd4-bebe-cf26b709d52b
-- title:
--   Join: aeval inter
-- statement:
--   The Join construction uses the aeval inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalPoly.lean#L12-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalPoly.lean#L12-L21

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

theorem PositivityTheory.ThKR.Join.aeval_inter {V M : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M] (j : V →ₗ[ℂ] M)
    (T : Module.End ℂ V) (C : Module.End ℂ M) (h : ∀ y, j (T y) = C (j y)) (g : Polynomial ℂ) (y : V) :
    j (Polynomial.aeval T g y) = Polynomial.aeval C g (j y) := by sorry
