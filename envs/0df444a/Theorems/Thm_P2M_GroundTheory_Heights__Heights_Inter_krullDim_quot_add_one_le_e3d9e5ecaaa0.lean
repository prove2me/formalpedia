-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_krullDim_quot_add_one_le_e3d9e5ecaaa0
-- name    : P2M_GroundTheory_Heights__Heights_Inter_krullDim_quot_add_one_le_e3d9e5ecaaa0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:48.646998+00:00
-- url     : https://prove2.me/theorems/a162a87f-e9b8-499b-98d4-2d9b47a59d58
-- title:
--   P2 M Ground Theory Heights  Heights Inter krull Dim quot add one le e3d9e5ecaaa0: P2 M Ground Theory Heights  Heights Inter krull Dim quot add one le e3d9e5ecaaa0
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter krull Dim quot add one le e3d9e5ecaaa0 construction uses the P2 M Ground Theory Heights  Heights Inter krull Dim quot add one le e3d9e5ecaaa0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/TableDegreeThreeBase.lean#L93-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/TableDegreeThreeBase.lean#L93-L105

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogFirstCoordinate
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
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
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_krullDim_quot_add_one_le_e3d9e5ecaaa0 {R : Type*} [CommRing R] {Q Q₂ : Ideal R} [Q.IsPrime] (hle : Q ≤ Q₂)
    {x : R} (hx : x ∈ Q₂) (hxQ : x ∉ Q) : ringKrullDim (R ⧸ Q₂) + 1 ≤ ringKrullDim (R ⧸ Q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«krullDim_quot_add_one_le» := P2M_GroundTheory_Heights__Heights_Inter_krullDim_quot_add_one_le_e3d9e5ecaaa0
