-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SheafLES___map_026ec4bafb10
-- name    : P2M_GlobalTheory_SheafLES___map_026ec4bafb10
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:40.533382+00:00
-- url     : https://prove2.me/theorems/eb381f55-929f-4401-890d-70b774016467
-- title:
--   P2 M Global Theory Sheaf LES   map 026ec4bafb10: P2 M Global Theory Sheaf LES   map 026ec4bafb10
-- statement:
--   The P2 M Global Theory Sheaf LES   map 026ec4bafb10 construction uses the P2 M Global Theory Sheaf LES   map 026ec4bafb10 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L179-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MapFOneInjectiveOfSectionsSurjective.lean#L179-L181

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

theorem P2M_GlobalTheory_SheafLES___map_026ec4bafb10 (n : ℕ) (U : C) (x : Sheaf.H'.{w'} S.X₂ n U) :
    δ hS n U (map S.g n U x) = 0 := by sorry

alias «GlobalTheory».«SheafLES».«δ_map» := P2M_GlobalTheory_SheafLES___map_026ec4bafb10
