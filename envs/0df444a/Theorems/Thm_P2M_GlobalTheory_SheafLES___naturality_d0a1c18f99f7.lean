-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SheafLES___naturality_d0a1c18f99f7
-- name    : P2M_GlobalTheory_SheafLES___naturality_d0a1c18f99f7
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:09.221845+00:00
-- url     : https://prove2.me/theorems/11e343e6-772d-4b07-8c9b-34b71c55c8e7
-- title:
--   P2 M Global Theory Sheaf LES   naturality d0a1c18f99f7: P2 M Global Theory Sheaf LES   naturality d0a1c18f99f7
-- statement:
--   The P2 M Global Theory Sheaf LES   naturality d0a1c18f99f7 construction uses the P2 M Global Theory Sheaf LES   naturality d0a1c18f99f7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L187-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L187-L195

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

theorem P2M_GlobalTheory_SheafLES___naturality_d0a1c18f99f7 {S₁ S₂ : ShortComplex (Sheaf J AddCommGrpCat.{v})} (h₁ : S₁.ShortExact)
    (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n : ℕ) (U : C) (x : Sheaf.H'.{w'} S₁.X₃ n U) :
    map φ.τ₁ (n + 1) U (δ h₁ n U x) = δ h₂ n U (map φ.τ₃ n U x) := by sorry

alias «GlobalTheory».«SheafLES».«δ_naturality» := P2M_GlobalTheory_SheafLES___naturality_d0a1c18f99f7
