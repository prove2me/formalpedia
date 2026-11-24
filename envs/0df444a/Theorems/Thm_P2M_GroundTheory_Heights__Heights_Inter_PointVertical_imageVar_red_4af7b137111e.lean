-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PointVertical_imageVar_red_4af7b137111e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PointVertical_imageVar_red_4af7b137111e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:25.448915+00:00
-- url     : https://prove2.me/theorems/78582f51-e9e9-427f-a7f6-10edc29526ef
-- title:
--   P2 M Ground Theory Heights  Heights Inter Point Vertical image Var red 4af7b137111e: P2 M Ground Theory Heights  Heights Inter Point Vertical image Var red 4af7b137111e
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Point Vertical image Var red 4af7b137111e construction uses the P2 M Ground Theory Heights  Heights Inter Point Vertical image Var red 4af7b137111e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsMultiProjPrimeImageZ.lean#L66-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsMultiProjPrimeImageZ.lean#L66-L76

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

theorem P2M_GroundTheory_Heights__Heights_Inter_PointVertical_imageVar_red_4af7b137111e [Fact p.Prime] (v : (Σ k, ι k) → (Σ k', ι' k')) {W : Ideal (MRing ι')}
    (hp : ((p : ℕ) : MRing ι') ∈ W) :
    imageVar (ZMod p) v (W.map (red p)) = (imageZ v W).map (red p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PointVertical».«imageVar_red» := P2M_GroundTheory_Heights__Heights_Inter_PointVertical_imageVar_red_4af7b137111e
