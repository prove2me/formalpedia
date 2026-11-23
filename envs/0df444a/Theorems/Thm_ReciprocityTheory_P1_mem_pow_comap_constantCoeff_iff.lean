-- Prove2me | Theorems.Thm_ReciprocityTheory_P1_mem_pow_comap_constantCoeff_iff
-- name    : ReciprocityTheory.P1.mem_pow_comap_constantCoeff_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:43.622372+00:00
-- url     : https://prove2.me/theorems/6e47e174-f108-4e15-940e-cc8779f742e7
-- title:
--   P1: mem pow comap constant Coeff iff
-- statement:
--   The P1 construction uses the mem pow comap constant Coeff iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AdicCompleteness/IsAdicCompleteComapConstantCoeff.lean#L29-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AdicCompleteness/IsAdicCompleteComapConstantCoeff.lean#L29-L65

import Mathlib
import Definitions.Def_ReciprocityTheory_AdicCompleteness_IsAdicCompleteComapConstantCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open PowerSeries IsLocalRing
noncomputable section
open ReciprocityTheory ReciprocityTheory.P1
variable {A : Type*} [CommRing A] (I : Ideal A)

theorem ReciprocityTheory.P1.mem_pow_comap_constantCoeff_iff (n : ℕ) (f : A⟦X⟧) :
    f ∈ I.comap (constantCoeff (R := A)) ^ n ↔ ∀ i, coeff i f ∈ I ^ (n - i) := by sorry
