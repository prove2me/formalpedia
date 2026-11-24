-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_IsPullHerm_isSmoothHerm_6e095cc736f9
-- name    : P2M_GroundTheory_Heights__Heights_Inter_IsPullHerm_isSmoothHerm_6e095cc736f9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:26.081346+00:00
-- url     : https://prove2.me/theorems/38e89258-b9f5-496a-91e6-b175d39749ed
-- title:
--   P2 M Ground Theory Heights  Heights Inter Is Pull Herm is Smooth Herm 6e095cc736f9: P2 M Ground Theory Heights  Heights Inter Is Pull Herm is Smooth Herm 6e095cc736f9
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Is Pull Herm is Smooth Herm 6e095cc736f9 construction uses the P2 M Ground Theory Heights  Heights Inter Is Pull Herm is Smooth Herm 6e095cc736f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/TableDegreeThreeBase.lean#L31-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/TableDegreeThreeBase.lean#L31-L39

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
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_IsPullHerm_isSmoothHerm_6e095cc736f9 {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {A : HermLine ι} {A' : HermLine ι'} (h : IsPullHerm κ v A A') (hA : IsSmoothHerm A) :
    IsSmoothHerm A' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«IsPullHerm».«isSmoothHerm» := P2M_GroundTheory_Heights__Heights_Inter_IsPullHerm_isSmoothHerm_6e095cc736f9
