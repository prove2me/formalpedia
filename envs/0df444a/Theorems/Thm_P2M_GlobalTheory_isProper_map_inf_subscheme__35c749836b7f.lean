-- Prove2me | Theorems.Thm_P2M_GlobalTheory_isProper_map_inf_subscheme__35c749836b7f
-- name    : P2M_GlobalTheory_isProper_map_inf_subscheme__35c749836b7f
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:11:57.696524+00:00
-- url     : https://prove2.me/theorems/9de062b6-4ed1-4426-94ce-766667e867d1
-- title:
--   P2 M Global Theory is Proper map inf subscheme  35c749836b7f: P2 M Global Theory is Proper map inf subscheme  35c749836b7f
-- statement:
--   The P2 M Global Theory is Proper map inf subscheme  35c749836b7f construction uses the P2 M Global Theory is Proper map inf subscheme  35c749836b7f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsProperInfIdealSheafImage.lean#L36-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsProperInfIdealSheafImage.lean#L36-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsProperInfIdealSheafImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
open GlobalTheory

theorem P2M_GlobalTheory_isProper_map_inf_subscheme__35c749836b7f : ∀ (S W W' : Scheme.{0}) (f : W ⟶ S) (π : W' ⟶ W),
    IsSeparated f → LocallyOfFiniteType f → ∀ (T' : W'.IdealSheafData) (T'' : W.IdealSheafData),
    IsProper (T'.subschemeι ≫ π ≫ f) → IsProper (T''.subschemeι ≫ f) →
    IsProper ((T'.map π ⊓ T'').subschemeι ≫ f) := by sorry

alias «GlobalTheory».«isProper_map_inf_subschemeι» := P2M_GlobalTheory_isProper_map_inf_subscheme__35c749836b7f
