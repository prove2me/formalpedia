-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_FibreMultiHomogeneous_exists_clear_79d57326ea96
-- name    : P2M_GroundTheory_Heights__Heights_Inter_FibreMultiHomogeneous_exists_clear_79d57326ea96
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:35.58692+00:00
-- url     : https://prove2.me/theorems/3c9e64ea-040d-4a21-a165-50894a3fcfdc
-- title:
--   P2 M Ground Theory Heights  Heights Inter Fibre Multi Homogeneous exists clear 79d57326ea96: P2 M Ground Theory Heights  Heights Inter Fibre Multi Homogeneous exists clear 79d57326ea96
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Fibre Multi Homogeneous exists clear 79d57326ea96 construction uses the P2 M Ground Theory Heights  Heights Inter Fibre Multi Homogeneous exists clear 79d57326ea96 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LiftZComponent.lean#L33-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LiftZComponent.lean#L33-L50

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

theorem P2M_GroundTheory_Heights__Heights_Inter_FibreMultiHomogeneous_exists_clear_79d57326ea96 [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] {v : (Σ k, ι k) → (Σ k', ι' k')} {W' : Ideal (MRing ι')} (G : GenFibre v W') {τ : Type*}
    (f : MvPolynomial τ G.Φ) : ∃ b : MRing ι, aeval G.x b ≠ 0 ∧
      ∃ F : MvPolynomial τ (MRing ι), C (aeval G.x b) * f = map (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«FibreMultiHomogeneous».«exists_clear» := P2M_GroundTheory_Heights__Heights_Inter_FibreMultiHomogeneous_exists_clear_79d57326ea96
