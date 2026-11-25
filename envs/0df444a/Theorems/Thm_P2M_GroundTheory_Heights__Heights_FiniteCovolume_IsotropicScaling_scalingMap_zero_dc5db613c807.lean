-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_zero_dc5db613c807
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_zero_dc5db613c807
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:17:42.729205+00:00
-- url     : https://prove2.me/theorems/0fc1db32-6f4c-51db-9ac4-12d1ff2ba4da
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling scaling Map zero dc5db613c807: P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling scaling Map zero dc5db613c807
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling scaling Map zero dc5db613c807 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling scaling Map zero dc5db613c807 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PIsotropicScaling.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PIsotropicScaling.lean#L27-L28

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
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
variable (h : HermitianForm F E W) {v w : W}

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_zero_dc5db613c807 : scalingMap h v w 0 0 = LinearMap.id := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«IsotropicScaling».«scalingMap_zero» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_zero_dc5db613c807
