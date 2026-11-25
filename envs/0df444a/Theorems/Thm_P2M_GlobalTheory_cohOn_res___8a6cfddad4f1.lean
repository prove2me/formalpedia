-- Prove2me | Theorems.Thm_P2M_GlobalTheory_cohOn_res___8a6cfddad4f1
-- name    : P2M_GlobalTheory_cohOn_res___8a6cfddad4f1
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:07:21.756285+00:00
-- url     : https://prove2.me/theorems/8fbdb842-dfda-44b5-881c-f3c2fbb3d90a
-- title:
--   P2 M Global Theory coh On res   8a6cfddad4f1: P2 M Global Theory coh On res   8a6cfddad4f1
-- statement:
--   The P2 M Global Theory coh On res   8a6cfddad4f1 construction uses the P2 M Global Theory coh On res   8a6cfddad4f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L183-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L183-L185

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
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
variable {U}

theorem P2M_GlobalTheory_cohOn_res___8a6cfddad4f1 {V : X.Opens} (h : V ≤ U) (x : cohOn S.X₃ U n) :
    res R S.X₁ h (n + 1) (δ R hS U n x) = δ R hS V n (res R S.X₃ h n x) := by sorry

alias «GlobalTheory».«cohOn».«res_δ» := P2M_GlobalTheory_cohOn_res___8a6cfddad4f1
