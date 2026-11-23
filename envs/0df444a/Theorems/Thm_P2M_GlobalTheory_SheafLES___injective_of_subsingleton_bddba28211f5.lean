-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SheafLES___injective_of_subsingleton_bddba28211f5
-- name    : P2M_GlobalTheory_SheafLES___injective_of_subsingleton_bddba28211f5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:44.474312+00:00
-- url     : https://prove2.me/theorems/53a7644f-9ef2-476d-8082-ae582cdaf8e6
-- title:
--   P2 M Global Theory Sheaf LES   injective of subsingleton bddba28211f5: P2 M Global Theory Sheaf LES   injective of subsingleton bddba28211f5
-- statement:
--   The P2 M Global Theory Sheaf LES   injective of subsingleton bddba28211f5 construction uses the P2 M Global Theory Sheaf LES   injective of subsingleton bddba28211f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L224-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L224-L229

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
variable {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)
include hS

theorem P2M_GlobalTheory_SheafLES___injective_of_subsingleton_bddba28211f5 (n : ℕ) (U : C)
    (h : Subsingleton (Sheaf.H'.{w'} S.X₂ n U)) : Function.Injective (δ.{w'} hS n U) := by sorry

alias «GlobalTheory».«SheafLES».«δ_injective_of_subsingleton» := P2M_GlobalTheory_SheafLES___injective_of_subsingleton_bddba28211f5
