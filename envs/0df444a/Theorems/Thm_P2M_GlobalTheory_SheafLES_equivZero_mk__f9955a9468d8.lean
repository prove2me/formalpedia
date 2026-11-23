-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SheafLES_equivZero_mk__f9955a9468d8
-- name    : P2M_GlobalTheory_SheafLES_equivZero_mk__f9955a9468d8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:23.651732+00:00
-- url     : https://prove2.me/theorems/a958411f-c641-4a84-aa1a-66af089ce444
-- title:
--   P2 M Global Theory Sheaf LES equiv Zero mk  f9955a9468d8: P2 M Global Theory Sheaf LES equiv Zero mk  f9955a9468d8
-- statement:
--   The P2 M Global Theory Sheaf LES equiv Zero mk  f9955a9468d8 construction uses the P2 M Global Theory Sheaf LES equiv Zero mk  f9955a9468d8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L121-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L121-L126

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe w' v u
open CategoryTheory Limits Abelian Opposite
noncomputable section
open GlobalTheory
open GlobalTheory.SheafLES
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
variable {F G K : Sheaf J AddCommGrpCat.{v}}

theorem P2M_GlobalTheory_SheafLES_equivZero_mk__f9955a9468d8 (U : C) (φ : (freeYoneda J).obj U ⟶ F) :
    equivZero.{w'} F U (Ext.mk₀ φ) = freeYonedaHomEquiv U F φ := by sorry

alias «GlobalTheory».«SheafLES».«equivZero_mk₀» := P2M_GlobalTheory_SheafLES_equivZero_mk__f9955a9468d8
