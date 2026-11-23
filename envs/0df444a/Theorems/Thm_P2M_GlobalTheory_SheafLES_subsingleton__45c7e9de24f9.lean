-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SheafLES_subsingleton__45c7e9de24f9
-- name    : P2M_GlobalTheory_SheafLES_subsingleton__45c7e9de24f9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:04.369722+00:00
-- url     : https://prove2.me/theorems/16af65fe-5e1d-4689-9cb6-dc7ccf2a47d8
-- title:
--   P2 M Global Theory Sheaf LES subsingleton  45c7e9de24f9: P2 M Global Theory Sheaf LES subsingleton  45c7e9de24f9
-- statement:
--   The P2 M Global Theory Sheaf LES subsingleton  45c7e9de24f9 construction uses the P2 M Global Theory Sheaf LES subsingleton  45c7e9de24f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L247-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L247-L251

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

theorem P2M_GlobalTheory_SheafLES_subsingleton__45c7e9de24f9 (n : ℕ) (U : C) (h₁ : Subsingleton (Sheaf.H'.{w'} S.X₁ n U))
    (h₃ : Subsingleton (Sheaf.H'.{w'} S.X₃ n U)) : Subsingleton (Sheaf.H'.{w'} S.X₂ n U) := by sorry

alias «GlobalTheory».«SheafLES».«subsingleton₂» := P2M_GlobalTheory_SheafLES_subsingleton__45c7e9de24f9
