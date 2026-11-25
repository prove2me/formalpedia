-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PointVertical_exists_dim_F_d97c61d7a449
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PointVertical_exists_dim_F_d97c61d7a449
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:07.762932+00:00
-- url     : https://prove2.me/theorems/d297b832-05ae-41ca-af1d-b00ce233745a
-- title:
--   P2 M Ground Theory Heights  Heights Inter Point Vertical exists dim F d97c61d7a449: P2 M Ground Theory Heights  Heights Inter Point Vertical exists dim F d97c61d7a449
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Point Vertical exists dim F d97c61d7a449 construction uses the P2 M Ground Theory Heights  Heights Inter Point Vertical exists dim F d97c61d7a449 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsMultiProjPrimeImageZ.lean#L98-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsMultiProjPrimeImageZ.lean#L98-L105

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

theorem P2M_GroundTheory_Heights__Heights_Inter_PointVertical_exists_dim_F_d97c61d7a449 {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (p : ℕ) [Fact p.Prime]
    (V : Ideal (MRingOver (ZMod p) ι)) (hV : IsMultiProjPrime V) :
    ∃ D : ℕ, Fintype.card K ≤ D ∧ ringKrullDim (MRingOver (ZMod p) ι ⧸ V) = D := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PointVertical».«exists_dim_F» := P2M_GroundTheory_Heights__Heights_Inter_PointVertical_exists_dim_F_d97c61d7a449
