-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_FibreMultiHomogeneous_aeval_liftZ_4942534c525a
-- name    : P2M_GroundTheory_Heights__Heights_Inter_FibreMultiHomogeneous_aeval_liftZ_4942534c525a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:56.030137+00:00
-- url     : https://prove2.me/theorems/bd7e1c15-df87-488e-b6cd-ef2f89e715a9
-- title:
--   P2 M Ground Theory Heights  Heights Inter Fibre Multi Homogeneous aeval lift Z 4942534c525a: P2 M Ground Theory Heights  Heights Inter Fibre Multi Homogeneous aeval lift Z 4942534c525a
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Fibre Multi Homogeneous aeval lift Z 4942534c525a construction uses the P2 M Ground Theory Heights  Heights Inter Fibre Multi Homogeneous aeval lift Z 4942534c525a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LiftZComponent.lean#L56-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LiftZComponent.lean#L56-L69

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

theorem P2M_GroundTheory_Heights__Heights_Inter_FibreMultiHomogeneous_aeval_liftZ_4942534c525a [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {W' : Ideal (MRing ι')} (G : GenFibre v W')
    (F : MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι)) :
    aeval G.x' (liftZ κ v F) = aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩)
      (map (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom F) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«FibreMultiHomogeneous».«aeval_liftZ» := P2M_GroundTheory_Heights__Heights_Inter_FibreMultiHomogeneous_aeval_liftZ_4942534c525a
