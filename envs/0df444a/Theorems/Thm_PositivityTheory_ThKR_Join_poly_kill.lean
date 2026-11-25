-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_Join_poly_kill
-- name    : PositivityTheory.ThKR.Join.poly_kill
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:47:12.881154+00:00
-- url     : https://prove2.me/theorems/59d73405-1066-55de-a04b-e65d26b1fc76
-- title:
--   Join: poly kill
-- statement:
--   The Join construction uses the poly kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalPoly.lean#L23-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalPoly.lean#L23-L34

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

theorem PositivityTheory.ThKR.Join.poly_kill {M : Type} [AddCommGroup M] [Module ℂ M] (C : Module.End ℂ M) (U : Submodule ℂ M) [FiniteDimensional ℂ U]
    (hU : ∀ y ∈ U, C y ∈ U) (hi : Function.Injective (C.restrict hU)) {x : M} (hx : x ∈ U) :
    ∃ g : Polynomial ℂ, g.eval 0 = 1 ∧ Polynomial.aeval C g x = 0 := by sorry
