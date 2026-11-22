-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_mem_riemannRochSpace_iff_regularAt_everywhere
-- name    : ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:49:32.462374+00:00
-- url     : https://prove2.me/theorems/0d8835d8-7374-4dc2-baaf-f4ddf4f08205
-- title:
--   Gal: mem riemann Roch Space iff regular At everywhere
-- statement:
--   The Gal construction uses the mem riemann Roch Space iff regular At everywhere property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/SeparatedDvrSecondCohomologyMem.lean#L40-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/SeparatedDvrSecondCohomologyMem.lean#L40-L40

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_SeparatedDvrSecondCohomologyMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Gal
set_option linter.unusedVariables false
noncomputable section
open Representation
variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
variable (rho : Representation R G M)

theorem ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere (m : M) : m ∈ H0 rho ↔ ∀ g, rho g m = m := by sorry
