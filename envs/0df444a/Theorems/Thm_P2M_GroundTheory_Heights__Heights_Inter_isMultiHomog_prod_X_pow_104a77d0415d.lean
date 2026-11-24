-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isMultiHomog_prod_X_pow_104a77d0415d
-- name    : P2M_GroundTheory_Heights__Heights_Inter_isMultiHomog_prod_X_pow_104a77d0415d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:20.182774+00:00
-- url     : https://prove2.me/theorems/def56054-7eac-4bbf-b06c-6c5a6a03e081
-- title:
--   P2 M Ground Theory Heights  Heights Inter is Multi Homog prod X pow 104a77d0415d: P2 M Ground Theory Heights  Heights Inter is Multi Homog prod X pow 104a77d0415d
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter is Multi Homog prod X pow 104a77d0415d construction uses the P2 M Ground Theory Heights  Heights Inter is Multi Homog prod X pow 104a77d0415d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/TableDegreeThreeBase.lean#L71-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/TableDegreeThreeBase.lean#L71-L91

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
omit [Fintype K]

theorem P2M_GroundTheory_Heights__Heights_Inter_isMultiHomog_prod_X_pow_104a77d0415d [DecidableEq K] {J : Type*} [Fintype J] (q : J → Σ k, ι k) (e : J → ℕ) :
    IsMultiHomog (∏ j, X (q j) ^ e j : MRing ι)
      (fun k => ∑ j ∈ Finset.univ.filter (fun j => (q j).1 = k), e j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«isMultiHomog_prod_X_pow» := P2M_GroundTheory_Heights__Heights_Inter_isMultiHomog_prod_X_pow_104a77d0415d
