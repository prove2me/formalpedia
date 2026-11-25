-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_isometry_7e0d595ba1e1
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_isometry_7e0d595ba1e1
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:39:13.553188+00:00
-- url     : https://prove2.me/theorems/162e51ec-adc3-45c9-8493-4b32cbc1d679
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling scaling Map isometry 7e0d595ba1e1: P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling scaling Map isometry 7e0d
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling scaling Map isometry 7e0d595ba1e1 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling scaling Map isometry 7e0d595ba1e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PIsotropicScaling.lean#L52-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PIsotropicScaling.lean#L52-L63

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
variable (hvv : h.toSesq v v = 0) (hww : h.toSesq w w = 0) (hvw : h.toSesq v w = 1)
  (hwv : h.toSesq w v = 1)
include hvv hww hvw hwv

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_isometry_7e0d595ba1e1 {α β : E} (hαβ : α + conj F E β + α * conj F E β = 0) (x y : W) :
    h.toSesq (scalingMap h v w α β x) (scalingMap h v w α β y) = h.toSesq x y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«IsotropicScaling».«scalingMap_isometry» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_isometry_7e0d595ba1e1
