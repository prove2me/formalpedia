-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_pairing_right_8c8b388a4a3d
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_pairing_right_8c8b388a4a3d
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:18:23.049289+00:00
-- url     : https://prove2.me/theorems/f53c4206-8d82-4467-a3a2-ea76f46d3385
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling pairing right 8c8b388a4a3d: P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling pairing right 8c8b388a4a3d
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling pairing right 8c8b388a4a3d construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling pairing right 8c8b388a4a3d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PIsotropicScaling.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PIsotropicScaling.lean#L35-L38

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_pairing_right_8c8b388a4a3d (hvv : h.toSesq v v = 0) (hvw : h.toSesq v w = 1) (α β : E) (x : W) :
    h.toSesq v (scalingMap h v w α β x) = (1 + β) * h.toSesq v x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«IsotropicScaling».«pairing_right» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_pairing_right_8c8b388a4a3d
