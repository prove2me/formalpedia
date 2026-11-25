-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_exists_nsmul_mem_b0df14af21b1
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_exists_nsmul_mem_b0df14af21b1
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:39:45.194117+00:00
-- url     : https://prove2.me/theorems/a467cfb9-3728-4d8b-84c5-cdb3ff53ec45
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling exists nsmul mem b0df14af21b1: P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling exists nsmul mem b0df14af21b1
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling exists nsmul mem b0df14af21b1 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling exists nsmul mem b0df14af21b1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PIsotropicScaling.lean#L78-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PIsotropicScaling.lean#L78-L100

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsVectorOrbits
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PIsotropicScaling
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.IsotropicScaling
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_exists_nsmul_mem_b0df14af21b1 {La : AddSubgroup W} (hLa : IsLattice E La) (w : W) :
    ∃ N : ℕ, 0 < N ∧ N • w ∈ La := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«IsotropicScaling».«exists_nsmul_mem» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_exists_nsmul_mem_b0df14af21b1
