-- Prove2me | Theorems.Thm_P2M_GlobalTheory_cohOn_subsingleton__cbacb3adb2f4
-- name    : P2M_GlobalTheory_cohOn_subsingleton__cbacb3adb2f4
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:40:26.105443+00:00
-- url     : https://prove2.me/theorems/cbb2d164-a57e-4b6d-91fd-f391e2a1c33e
-- title:
--   P2 M Global Theory coh On subsingleton  cbacb3adb2f4: P2 M Global Theory coh On subsingleton  cbacb3adb2f4
-- statement:
--   The P2 M Global Theory coh On subsingleton  cbacb3adb2f4 construction uses the P2 M Global Theory coh On subsingleton  cbacb3adb2f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L203-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L203-L205

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_P2M_GlobalTheory_SheafLES_subsingleton__45c7e9de24f9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Module
universe t v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}}
open GlobalTheory.cohOn
variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
  {S : ShortComplex X.Modules} (hS : S.ShortExact)
variable (U : X.Opens) (n : ℕ)
include hS

theorem P2M_GlobalTheory_cohOn_subsingleton__cbacb3adb2f4 (h₁ : Subsingleton (cohOn S.X₁ U n)) (h₃ : Subsingleton (cohOn S.X₃ U n)) :
    Subsingleton (cohOn S.X₂ U n) := by sorry

alias «GlobalTheory».«cohOn».«subsingleton₂» := P2M_GlobalTheory_cohOn_subsingleton__cbacb3adb2f4
