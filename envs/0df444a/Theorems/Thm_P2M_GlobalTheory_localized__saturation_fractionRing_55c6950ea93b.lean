-- Prove2me | Theorems.Thm_P2M_GlobalTheory_localized__saturation_fractionRing_55c6950ea93b
-- name    : P2M_GlobalTheory_localized__saturation_fractionRing_55c6950ea93b
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:07:07.436266+00:00
-- url     : https://prove2.me/theorems/256e9548-c444-5963-a076-487654be2be1
-- title:
--   P2 M Global Theory localized  saturation fraction Ring 55c6950ea93b: P2 M Global Theory localized  saturation fraction Ring 55c6950ea93b
-- statement:
--   The P2 M Global Theory localized  saturation fraction Ring 55c6950ea93b construction uses the P2 M Global Theory localized  saturation fraction Ring 55c6950ea93b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L809-L811
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L809-L811

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Pointwise
open GlobalTheory
variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  (f : M →ₗ[R] V) [IsLocalizedModule R⁰ f]

theorem P2M_GlobalTheory_localized__saturation_fractionRing_55c6950ea93b (N : Submodule R M) :
    (saturation N).localized' K R⁰ f = N.localized' K R⁰ f := by sorry

alias «GlobalTheory».«localized'_saturation_fractionRing» := P2M_GlobalTheory_localized__saturation_fractionRing_55c6950ea93b
