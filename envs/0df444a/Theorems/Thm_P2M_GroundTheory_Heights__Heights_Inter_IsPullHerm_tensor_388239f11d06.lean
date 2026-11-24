-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_IsPullHerm_tensor_388239f11d06
-- name    : P2M_GroundTheory_Heights__Heights_Inter_IsPullHerm_tensor_388239f11d06
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:41.41615+00:00
-- url     : https://prove2.me/theorems/7c940398-a7c5-4316-9ab3-9feaa24bbf0f
-- title:
--   P2 M Ground Theory Heights  Heights Inter Is Pull Herm tensor 388239f11d06: P2 M Ground Theory Heights  Heights Inter Is Pull Herm tensor 388239f11d06
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Is Pull Herm tensor 388239f11d06 construction uses the P2 M Ground Theory Heights  Heights Inter Is Pull Herm tensor 388239f11d06 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/TableDegreeThreeBase.lean#L54-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/TableDegreeThreeBase.lean#L54-L61

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
omit [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_IsPullHerm_tensor_388239f11d06 {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {A B : HermLine ι}
    {A' B' : HermLine ι'} (hA : IsPullHerm κ v A A') (hB : IsPullHerm κ v B B') :
    IsPullHerm κ v (A.tensor B) (A'.tensor B') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«IsPullHerm».«tensor» := P2M_GroundTheory_Heights__Heights_Inter_IsPullHerm_tensor_388239f11d06
