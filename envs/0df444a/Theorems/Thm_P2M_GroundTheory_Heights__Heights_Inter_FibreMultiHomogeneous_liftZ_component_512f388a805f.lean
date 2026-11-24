-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_FibreMultiHomogeneous_liftZ_component_512f388a805f
-- name    : P2M_GroundTheory_Heights__Heights_Inter_FibreMultiHomogeneous_liftZ_component_512f388a805f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:53.815122+00:00
-- url     : https://prove2.me/theorems/bd8a6819-9049-45cf-a69e-35b8139e4b65
-- title:
--   P2 M Ground Theory Heights  Heights Inter Fibre Multi Homogeneous lift Z component 512f388a805f: P2 M Ground Theory Heights  Heights Inter Fibre Multi Homogeneous lift Z component 512f388a805f
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Fibre Multi Homogeneous lift Z component 512f388a805f construction uses the P2 M Ground Theory Heights  Heights Inter Fibre Multi Homogeneous lift Z component 512f388a805f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LiftZComponent.lean#L71-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LiftZComponent.lean#L71-L109

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

theorem P2M_GroundTheory_Heights__Heights_Inter_FibreMultiHomogeneous_liftZ_component_512f388a805f [Fintype K'] [∀ k, Fintype (ι' k)] [DecidableEq K'] {κ : K → K'} [DecidableEq (FibreBlock κ)] {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hv : IsBlockMap κ v) (k : FibreBlock κ) (n : ℕ) (F : MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι)) :
    weightedHomogeneousComponent (cycBlockWt k.1) n (liftZ κ v F) =
      liftZ κ v (weightedHomogeneousComponent (cycBlockWt k) n F) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«FibreMultiHomogeneous».«liftZ_component» := P2M_GroundTheory_Heights__Heights_Inter_FibreMultiHomogeneous_liftZ_component_512f388a805f
