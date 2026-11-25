-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PointVertical_isMultiHomog_rename_075ef48305ef
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PointVertical_isMultiHomog_rename_075ef48305ef
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:41.560525+00:00
-- url     : https://prove2.me/theorems/f0bee73f-01b6-4c8d-b1e4-a93606494aff
-- title:
--   P2 M Ground Theory Heights  Heights Inter Point Vertical is Multi Homog rename 075ef48305ef: P2 M Ground Theory Heights  Heights Inter Point Vertical is Multi Homog rename 075ef48305ef
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Point Vertical is Multi Homog rename 075ef48305ef construction uses the P2 M Ground Theory Heights  Heights Inter Point Vertical is Multi Homog rename 075ef48305ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsMultiProjPrimeImageZ.lean#L78-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsMultiProjPrimeImageZ.lean#L78-L87

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogIdealChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogFirstCoordinate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiProjPrimeImageZ
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.PointVertical
variable {K : Type} {ι : K → Type} (p : ℕ)
variable {K' : Type} {ι' : K' → Type}

theorem P2M_GroundTheory_Heights__Heights_Inter_PointVertical_isMultiHomog_rename_075ef48305ef [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {t : MRing ι} {a : K → ℕ} (ht : IsMultiHomog t a) :
    IsMultiHomog (rename v t) (Function.extend κ a 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PointVertical».«isMultiHomog_rename» := P2M_GroundTheory_Heights__Heights_Inter_PointVertical_isMultiHomog_rename_075ef48305ef
