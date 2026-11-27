-- Prove2me | Theorems.Thm_P2M_GlobalTheory_localized__saturationIn_2c26f398bac4
-- name    : P2M_GlobalTheory_localized__saturationIn_2c26f398bac4
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:07:13.577941+00:00
-- url     : https://prove2.me/theorems/5812fb1f-6d01-44c0-a329-4380f36d3745
-- title:
--   P2 M Global Theory localized  saturation In 2c26f398bac4: P2 M Global Theory localized  saturation In 2c26f398bac4
-- statement:
--   The P2 M Global Theory localized  saturation In 2c26f398bac4 construction uses the P2 M Global Theory localized  saturation In 2c26f398bac4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L625-L628
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean#L625-L628

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
  (S : Type*) [CommRing S] [Algebra R S] (p : Submonoid R) [IsLocalization p S]
  {Mp : Type*} [AddCommGroup Mp] [Module R Mp] [Module S Mp] [IsScalarTower R S Mp]
  (f : M →ₗ[R] Mp) [IsLocalizedModule p f]

theorem P2M_GlobalTheory_localized__saturationIn_2c26f398bac4 (hp : p ≤ R⁰) (P N : Submodule R M) :
    (saturationIn P N).localized' S p f =
      saturationIn (P.localized' S p f) (N.localized' S p f) := by sorry

alias «GlobalTheory».«localized'_saturationIn» := P2M_GlobalTheory_localized__saturationIn_2c26f398bac4
