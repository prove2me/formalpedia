-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_FibreMultiHomogeneous_component_map_472fbc4efe30
-- name    : P2M_GroundTheory_Heights__Heights_Inter_FibreMultiHomogeneous_component_map_472fbc4efe30
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:09.296885+00:00
-- url     : https://prove2.me/theorems/60e43168-b49a-4546-9597-f589e018f78f
-- title:
--   P2 M Ground Theory Heights  Heights Inter Fibre Multi Homogeneous component map 472fbc4efe30: P2 M Ground Theory Heights  Heights Inter Fibre Multi Homogeneous component map 472fbc4efe30
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Fibre Multi Homogeneous component map 472fbc4efe30 construction uses the P2 M Ground Theory Heights  Heights Inter Fibre Multi Homogeneous component map 472fbc4efe30 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LiftZComponent.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LiftZComponent.lean#L19-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreLast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiProjPrimeImageZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LiftZComponent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open GroundTheory.Heights₂.Heights.Inter.FibreMultiHomogeneous
variable {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}

theorem P2M_GroundTheory_Heights__Heights_Inter_FibreMultiHomogeneous_component_map_472fbc4efe30 {σ R S : Type*} [CommSemiring R] [CommSemiring S] (g : R →+* S) (w : σ → ℕ) (n : ℕ)
    (F : MvPolynomial σ R) :
    weightedHomogeneousComponent w n (map g F) = map g (weightedHomogeneousComponent w n F) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«FibreMultiHomogeneous».«component_map» := P2M_GroundTheory_Heights__Heights_Inter_FibreMultiHomogeneous_component_map_472fbc4efe30
