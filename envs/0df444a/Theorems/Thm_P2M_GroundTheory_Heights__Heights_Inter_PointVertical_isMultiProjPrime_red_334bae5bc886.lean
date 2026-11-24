-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PointVertical_isMultiProjPrime_red_334bae5bc886
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PointVertical_isMultiProjPrime_red_334bae5bc886
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:25:42.823596+00:00
-- url     : https://prove2.me/theorems/a601fc3f-1ae7-45c0-9f7f-96dd20b3d33f
-- title:
--   P2 M Ground Theory Heights  Heights Inter Point Vertical is Multi Proj Prime red 334bae5bc886: P2 M Ground Theory Heights  Heights Inter Point Vertical is Multi Proj Prime red 334bae5bc886
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Point Vertical is Multi Proj Prime red 334bae5bc886 construction uses the P2 M Ground Theory Heights  Heights Inter Point Vertical is Multi Proj Prime red 334bae5bc886 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsMultiProjPrimeImageZ.lean#L51-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsMultiProjPrimeImageZ.lean#L51-L62

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

theorem P2M_GroundTheory_Heights__Heights_Inter_PointVertical_isMultiProjPrime_red_334bae5bc886 [∀ k, Fintype (ι k)] {J : Ideal (MRing ι)} (hJ : IsMultiProjPrime J)
    (hp : ((p : ℕ) : MRing ι) ∈ J) : IsMultiProjPrime (J.map (red p)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PointVertical».«isMultiProjPrime_red» := P2M_GroundTheory_Heights__Heights_Inter_PointVertical_isMultiProjPrime_red_334bae5bc886
