-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SheafLES___res_2b8f5cf68032
-- name    : P2M_GlobalTheory_SheafLES___res_2b8f5cf68032
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:04.948045+00:00
-- url     : https://prove2.me/theorems/70b0db75-e54e-42e5-b5e1-9f776e02c6d6
-- title:
--   P2 M Global Theory Sheaf LES   res 2b8f5cf68032: P2 M Global Theory Sheaf LES   res 2b8f5cf68032
-- statement:
--   The P2 M Global Theory Sheaf LES   res 2b8f5cf68032 construction uses the P2 M Global Theory Sheaf LES   res 2b8f5cf68032 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L197-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L197-L203

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

theorem P2M_GlobalTheory_SheafLES___res_2b8f5cf68032 (n : ℕ) {U V : C} (i : V ⟶ U) (x : Sheaf.H'.{w'} S.X₃ n U) :
    res S.X₁ (n + 1) i (δ hS n U x) = δ hS n V (res S.X₃ n i x) := by sorry

alias «GlobalTheory».«SheafLES».«δ_res» := P2M_GlobalTheory_SheafLES___res_2b8f5cf68032
