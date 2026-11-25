-- Prove2me | Theorems.Thm_P2M_GlobalTheory_isGradedMap_lsmul__da4273aa92c0
-- name    : P2M_GlobalTheory_isGradedMap_lsmul__da4273aa92c0
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:07:14.030055+00:00
-- url     : https://prove2.me/theorems/550188e9-1b11-4f45-a692-587eff3024db
-- title:
--   P2 M Global Theory is Graded Map lsmul  da4273aa92c0: P2 M Global Theory is Graded Map lsmul  da4273aa92c0
-- statement:
--   The P2 M Global Theory is Graded Map lsmul  da4273aa92c0 construction uses the P2 M Global Theory is Graded Map lsmul  da4273aa92c0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L292-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsGradedMapLinearCombination.lean#L292-L295

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open DirectSum MvPolynomial
noncomputable section
open GlobalTheory
open GradedHilbert
variable {ι : Type*} {R : Type*} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  {P : Type*} [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]

theorem P2M_GlobalTheory_isGradedMap_lsmul__da4273aa92c0 (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] {p : MvPolynomial ι R}
    {d : ℤ} (hp : p ∈ polyGrading ι R d) :
    IsGradedMap (grShift ℳ (-d)) ℳ (LinearMap.lsmul (MvPolynomial ι R) M p) := by sorry

alias «GlobalTheory».«isGradedMap_lsmul'» := P2M_GlobalTheory_isGradedMap_lsmul__da4273aa92c0
