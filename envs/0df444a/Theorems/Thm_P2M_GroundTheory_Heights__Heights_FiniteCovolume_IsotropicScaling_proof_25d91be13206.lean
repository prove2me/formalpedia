-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_proof_25d91be13206
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_proof_25d91be13206
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:57:39.979887+00:00
-- url     : https://prove2.me/theorems/4b848def-2d0d-50d3-babd-4ead19ea473b
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling proof 25d91be13206: P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling proof 25d91be13206
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling proof 25d91be13206 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling proof 25d91be13206 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PIsotropicScaling.lean#L151-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PIsotropicScaling.lean#L151-L197

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_proof_25d91be13206 (h : HermitianForm F E W) (h₁ : WittPartner.Statement h) :
    IsotropicScaling.Statement h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«IsotropicScaling».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_proof_25d91be13206
