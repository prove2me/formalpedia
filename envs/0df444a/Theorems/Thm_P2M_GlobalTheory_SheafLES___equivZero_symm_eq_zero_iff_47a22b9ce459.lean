-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SheafLES___equivZero_symm_eq_zero_iff_47a22b9ce459
-- name    : P2M_GlobalTheory_SheafLES___equivZero_symm_eq_zero_iff_47a22b9ce459
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:41.105565+00:00
-- url     : https://prove2.me/theorems/060c4b3c-c37b-4877-a880-b9072e6906bb
-- title:
--   P2 M Global Theory Sheaf LES   equiv Zero symm eq zero iff 47a22b9ce459: P2 M Global Theory Sheaf LES   equiv Zero symm eq zero iff 47a22b9ce459
-- statement:
--   The P2 M Global Theory Sheaf LES   equiv Zero symm eq zero iff 47a22b9ce459 construction uses the P2 M Global Theory Sheaf LES   equiv Zero symm eq zero iff 47a22b9ce459 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L207-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L207-L214

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

theorem P2M_GlobalTheory_SheafLES___equivZero_symm_eq_zero_iff_47a22b9ce459 (U : C) (s : S.X₃.obj.obj (op U)) :
    δ.{w'} hS 0 U ((equivZero S.X₃ U).symm s) = 0 ↔ ∃ t, S.g.hom.app (op U) t = s := by sorry

alias «GlobalTheory».«SheafLES».«δ_equivZero_symm_eq_zero_iff» := P2M_GlobalTheory_SheafLES___equivZero_symm_eq_zero_iff_47a22b9ce459
