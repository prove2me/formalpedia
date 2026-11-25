-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_isUnit_map_of_mem_nonZeroDivisors_tensor__ba12e47f1fb4
-- name    : P2M_GlobalTheory_T_isUnit_map_of_mem_nonZeroDivisors_tensor__ba12e47f1fb4
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:10:09.753266+00:00
-- url     : https://prove2.me/theorems/c084ccec-8579-41bb-9a26-ecf68c376c4a
-- title:
--   P2 M Global Theory T is Unit map of mem non Zero Divisors tensor  ba12e47f1fb4: P2 M Global Theory T is Unit map of mem non Zero Divisors tensor  ba12e47f1fb4
-- statement:
--   The P2 M Global Theory T is Unit map of mem non Zero Divisors tensor  ba12e47f1fb4 construction uses the P2 M Global Theory T is Unit map of mem non Zero Divisors tensor  ba12e47f1fb4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsUnitMapOfMemNonZeroDivisorsTensorStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsUnitMapOfMemNonZeroDivisorsTensorStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsUnitMapOfMemNonZeroDivisorsTensor
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsUnitMapOfMemNonZeroDivisorsTensorStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_isUnit_map_of_mem_nonZeroDivisors_tensor__ba12e47f1fb4 : ∀ (T U C F K L : Type) [CommRing T] [IsDomain T] [CommRing U] [IsDomain U] [CommRing C] [IsDomain C] [Field F] [Field K] [Field L] [Algebra T U] [Algebra T C] [Algebra T F] [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra U L] [IsFractionRing U L] [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Algebra T L] [Algebra F L] [IsScalarTower T U L] [IsScalarTower T F L] [Module.Finite T C] (φ : U ⊗[T] C →+* L ⊗[F] K), Function.Injective φ → (∀ u c, φ (u ⊗ₜ c) = algebraMap U L u ⊗ₜ algebraMap C K c) → ∀ s ∈ nonZeroDivisors (U ⊗[T] C), IsUnit (φ s) := by sorry

alias «GlobalTheory».«T».«isUnit_map_of_mem_nonZeroDivisors_tensor'» := P2M_GlobalTheory_T_isUnit_map_of_mem_nonZeroDivisors_tensor__ba12e47f1fb4
