-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SheafLES_subsingleton__430f6995ae54
-- name    : P2M_GlobalTheory_SheafLES_subsingleton__430f6995ae54
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:17.799954+00:00
-- url     : https://prove2.me/theorems/f491337d-1f85-446a-8c79-ca2a6f62e4b9
-- title:
--   P2 M Global Theory Sheaf LES subsingleton  430f6995ae54: P2 M Global Theory Sheaf LES subsingleton  430f6995ae54
-- statement:
--   The P2 M Global Theory Sheaf LES subsingleton  430f6995ae54 construction uses the P2 M Global Theory Sheaf LES subsingleton  430f6995ae54 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L257-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L257-L260

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

theorem P2M_GlobalTheory_SheafLES_subsingleton__430f6995ae54 (n : ℕ) (U : C) (h₃ : Subsingleton (Sheaf.H'.{w'} S.X₃ n U))
    (h₂ : Subsingleton (Sheaf.H'.{w'} S.X₂ (n + 1) U)) :
    Subsingleton (Sheaf.H'.{w'} S.X₁ (n + 1) U) := by sorry

alias «GlobalTheory».«SheafLES».«subsingleton₁» := P2M_GlobalTheory_SheafLES_subsingleton__430f6995ae54
