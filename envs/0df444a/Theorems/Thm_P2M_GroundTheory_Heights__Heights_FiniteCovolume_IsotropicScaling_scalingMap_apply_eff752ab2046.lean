-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_apply_eff752ab2046
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_apply_eff752ab2046
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:08:34.220551+00:00
-- url     : https://prove2.me/theorems/353a47d0-2d6e-4564-8553-25fc14fad28c
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling scaling Map apply eff752ab2046: P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling scaling Map apply eff752ab20
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling scaling Map apply eff752ab2046 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling scaling Map apply eff752ab2046 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PIsotropicScaling.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PIsotropicScaling.lean#L23-L25

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_apply_eff752ab2046 (α β : E) (x : W) :
    scalingMap h v w α β x = x + (α * h.toSesq w x) • v + (β * h.toSesq v x) • w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«IsotropicScaling».«scalingMap_apply» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_apply_eff752ab2046
