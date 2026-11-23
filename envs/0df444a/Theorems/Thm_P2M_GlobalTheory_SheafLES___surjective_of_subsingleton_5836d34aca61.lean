-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SheafLES___surjective_of_subsingleton_5836d34aca61
-- name    : P2M_GlobalTheory_SheafLES___surjective_of_subsingleton_5836d34aca61
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:08.447822+00:00
-- url     : https://prove2.me/theorems/5877b52c-55ef-474f-b16b-8a6582be6950
-- title:
--   P2 M Global Theory Sheaf LES   surjective of subsingleton 5836d34aca61: P2 M Global Theory Sheaf LES   surjective of subsingleton 5836d34aca61
-- statement:
--   The P2 M Global Theory Sheaf LES   surjective of subsingleton 5836d34aca61 construction uses the P2 M Global Theory Sheaf LES   surjective of subsingleton 5836d34aca61 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L220-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L220-L222

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

theorem P2M_GlobalTheory_SheafLES___surjective_of_subsingleton_5836d34aca61 (n : ℕ) (U : C)
    (h : Subsingleton (Sheaf.H'.{w'} S.X₂ (n + 1) U)) : Function.Surjective (δ.{w'} hS n U) := by sorry

alias «GlobalTheory».«SheafLES».«δ_surjective_of_subsingleton» := P2M_GlobalTheory_SheafLES___surjective_of_subsingleton_5836d34aca61
