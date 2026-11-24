-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Ex_NumD_Int_norm___8f2d6a954aa8
-- name    : P2M_GlobalTheory_Ex_NumD_Int_norm___8f2d6a954aa8
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:43:41.552108+00:00
-- url     : https://prove2.me/theorems/d5a6a569-7af9-4c37-a328-1f6777a9d0cd
-- title:
--   P2 M Global Theory Ex Num D Int norm   8f2d6a954aa8: P2 M Global Theory Ex Num D Int norm   8f2d6a954aa8
-- statement:
--   The P2 M Global Theory Ex Num D Int norm   8f2d6a954aa8 construction uses the P2 M Global Theory Ex Num D Int norm   8f2d6a954aa8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/NormRepGeneratorsAndThetaSeriesTerm.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/NormRepGeneratorsAndThetaSeriesTerm.lean#L22-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.NumD GlobalTheory.Ex.NumD.Int
variable {C : Type} [NormedField C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}

theorem P2M_GlobalTheory_Ex_NumD_Int_norm___8f2d6a954aa8 (h : N.Int q) (a b : N.X) : ‖(N.τ a b : C)‖ = Real.exp (-QuadraticMap.polar q a b) := by sorry

alias «GlobalTheory».«Ex».«NumD».«Int».«norm_τ» := P2M_GlobalTheory_Ex_NumD_Int_norm___8f2d6a954aa8
