-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_FibreMultiHomogeneous_component_mem_d0b72ecac493
-- name    : P2M_GroundTheory_Heights__Heights_Inter_FibreMultiHomogeneous_component_mem_d0b72ecac493
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:02:34.773149+00:00
-- url     : https://prove2.me/theorems/903a1b4a-f390-4e59-8fc5-5f7d9cc7c725
-- title:
--   P2 M Ground Theory Heights  Heights Inter Fibre Multi Homogeneous component mem d0b72ecac493: P2 M Ground Theory Heights  Heights Inter Fibre Multi Homogeneous component mem d0b72ecac493
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Fibre Multi Homogeneous component mem d0b72ecac493 construction uses the P2 M Ground Theory Heights  Heights Inter Fibre Multi Homogeneous component mem d0b72ecac493 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LiftZComponent.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LiftZComponent.lean#L26-L31

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

theorem P2M_GroundTheory_Heights__Heights_Inter_FibreMultiHomogeneous_component_mem_d0b72ecac493 [Fintype K'] [∀ k, Fintype (ι' k)] {p : ℕ} {W' : Ideal (MRing ι')} (hp : ((p : ℕ) : MRing ι') ∈ W')
    (hW : IsMultiHomogIdeal (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p))))) [DecidableEq K'] (k : K')
    (n : ℕ) {g : MRing ι'} (hg : g ∈ W') : weightedHomogeneousComponent (cycBlockWt k) n g ∈ W' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«FibreMultiHomogeneous».«component_mem» := P2M_GroundTheory_Heights__Heights_Inter_FibreMultiHomogeneous_component_mem_d0b72ecac493
