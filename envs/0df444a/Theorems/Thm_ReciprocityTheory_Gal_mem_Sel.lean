-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_mem_Sel
-- name    : ReciprocityTheory.Gal.mem_Sel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:05:58.502435+00:00
-- url     : https://prove2.me/theorems/7acd7cb2-b67f-43db-82ea-eef7ceeeb51c
-- title:
--   Gal: mem Sel
-- statement:
--   The Gal construction uses the mem Sel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/ContinuousConstSMulQuotient.lean#L164-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/ContinuousConstSMulQuotient.lean#L164-L166

import Definitions.Def_ReciprocityTheory_GaloisValuations_SeparatedDvrSecondCohomologyMem
import Definitions.Def_ReciprocityTheory_GaloisValuations_ContinuousConstSMulQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Gal
noncomputable section
open Representation
variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
variable (rho : Representation R G M)
variable {I : Type*} {D : I → Type*} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
  (phi : ∀ i, D i →* G) (hphi : ∀ i, Continuous (phi i))

theorem ReciprocityTheory.Gal.mem_Sel (L : LocCond rho phi) (x : H1 rho) :
    x ∈ Sel rho phi hphi L ↔ ∀ i, resH1 rho (phi i) (hphi i) x ∈ L i := by sorry
