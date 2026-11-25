-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_comp_dd4b298a92c9
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_comp_dd4b298a92c9
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:39:34.043545+00:00
-- url     : https://prove2.me/theorems/f4c0f74d-4559-4a24-a87c-b43146c23681
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling scaling Map comp dd4b298a92c9: P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling scaling Map comp dd4b298a92c9
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling scaling Map comp dd4b298a92c9 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling scaling Map comp dd4b298a92c9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PIsotropicScaling.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PIsotropicScaling.lean#L44-L50

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_comp_dd4b298a92c9 (α β α' β' : E) :
    scalingMap h v w α β ∘ₗ scalingMap h v w α' β' =
      scalingMap h v w (α + α' + α * α') (β + β' + β * β') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«IsotropicScaling».«scalingMap_comp» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_comp_dd4b298a92c9
