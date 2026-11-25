-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_mem_2f9ce7653ab7
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_mem_2f9ce7653ab7
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:40:19.29436+00:00
-- url     : https://prove2.me/theorems/30a395ef-bb55-4e1e-b75d-401ce7c0df33
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling scaling Map mem 2f9ce7653ab7: P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling scaling Map mem 2f9ce7653ab7
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling scaling Map mem 2f9ce7653ab7 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Isotropic Scaling scaling Map mem 2f9ce7653ab7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PIsotropicScaling.lean#L109-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PIsotropicScaling.lean#L109-L141

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
omit [NumberField E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_mem_2f9ce7653ab7 (h : HermitianForm F E W) {La : AddSubgroup W} (hLa : IsLattice E La)
    (hint : IsIntegralOn h La) {v w : W} (hv : v ∈ La) {N : ℕ} (hNw : N • w ∈ La)
    {u : (𝓞 E)ˣ} (hu : u ∈ congruenceUnits E N) {x : W} (hx : x ∈ La) :
    scalingMap h v w (((u : 𝓞 E) : E) - 1) ((conj F E ((u : 𝓞 E) : E))⁻¹ - 1) x ∈ La := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«IsotropicScaling».«scalingMap_mem» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_mem_2f9ce7653ab7
