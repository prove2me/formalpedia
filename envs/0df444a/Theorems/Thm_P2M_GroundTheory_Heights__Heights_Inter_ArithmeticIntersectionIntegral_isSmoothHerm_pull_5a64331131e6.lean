-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionIntegral_isSmoothHerm_pull_5a64331131e6
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionIntegral_isSmoothHerm_pull_5a64331131e6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:50.993515+00:00
-- url     : https://prove2.me/theorems/6c654311-b08e-4d05-946d-631f5b265a08
-- title:
--   P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Integral is Smooth Herm pull 5a64331131e6: P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Integral is Smooth Herm p
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Integral is Smooth Herm pull 5a64331131e6 construction uses the P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Integral is Smooth Herm pull 5a64331131e6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PtsIntegralLogNormRat.lean#L78-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PtsIntegralLogNormRat.lean#L78-L94

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsFieldIntersectionNoBlockFam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PtsIntegralLogNormRat
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
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2
  ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionIntegral
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionIntegral_isSmoothHerm_pull_5a64331131e6 {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {A : HermLine ι} {A' : HermLine ι'} (hA : IsSmoothHerm A) (h : IsPullHerm κ v A A') :
    IsSmoothHerm A' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ArithmeticIntersectionIntegral».«isSmoothHerm_pull» := P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionIntegral_isSmoothHerm_pull_5a64331131e6
