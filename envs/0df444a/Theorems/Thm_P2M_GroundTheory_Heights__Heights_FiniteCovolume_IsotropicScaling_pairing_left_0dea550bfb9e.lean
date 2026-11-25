-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_pairing_left_0dea550bfb9e
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_pairing_left_0dea550bfb9e
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:38:43.174853+00:00
-- url     : https://prove2.me/theorems/35a87296-e8be-5d75-a4ab-ac5eb3e09bb2
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling pairing left 0dea550bfb9e: P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling pairing left 0dea550bfb9e
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling pairing left 0dea550bfb9e construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling pairing left 0dea550bfb9e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PIsotropicScaling.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PIsotropicScaling.lean#L30-L33

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_pairing_left_0dea550bfb9e (hww : h.toSesq w w = 0) (hwv : h.toSesq w v = 1) (α β : E) (x : W) :
    h.toSesq w (scalingMap h v w α β x) = (1 + α) * h.toSesq w x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«IsotropicScaling».«pairing_left» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_pairing_left_0dea550bfb9e
