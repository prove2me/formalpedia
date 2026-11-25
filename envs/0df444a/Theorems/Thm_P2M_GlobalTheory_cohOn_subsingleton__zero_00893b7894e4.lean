-- Prove2me | Theorems.Thm_P2M_GlobalTheory_cohOn_subsingleton__zero_00893b7894e4
-- name    : P2M_GlobalTheory_cohOn_subsingleton__zero_00893b7894e4
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:07:31.22345+00:00
-- url     : https://prove2.me/theorems/fce8f809-9b71-49e6-bc6d-939851003189
-- title:
--   P2 M Global Theory coh On subsingleton  zero 00893b7894e4: P2 M Global Theory coh On subsingleton  zero 00893b7894e4
-- statement:
--   The P2 M Global Theory coh On subsingleton  zero 00893b7894e4 construction uses the P2 M Global Theory coh On subsingleton  zero 00893b7894e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L215-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L215-L216

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_P2M_GlobalTheory_SheafLES_subsingleton__zero_1933a20f9277

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

theorem P2M_GlobalTheory_cohOn_subsingleton__zero_00893b7894e4 (h₂ : Subsingleton (cohOn S.X₂ U 0)) : Subsingleton (cohOn S.X₁ U 0) := by sorry

alias «GlobalTheory».«cohOn».«subsingleton₁_zero» := P2M_GlobalTheory_cohOn_subsingleton__zero_00893b7894e4
