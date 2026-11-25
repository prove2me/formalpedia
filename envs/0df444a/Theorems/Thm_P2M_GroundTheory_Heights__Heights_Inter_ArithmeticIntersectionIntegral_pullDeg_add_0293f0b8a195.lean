-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionIntegral_pullDeg_add_0293f0b8a195
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionIntegral_pullDeg_add_0293f0b8a195
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:20:37.526872+00:00
-- url     : https://prove2.me/theorems/a3875eb9-9309-4c93-b47d-1b31cf55ac7d
-- title:
--   P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Integral pull Deg add 0293f0b8a195: P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Integral pull Deg add 0293f0b8a1
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Integral pull Deg add 0293f0b8a195 construction uses the P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Integral pull Deg add 0293f0b8a195 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PtsIntegralLogNormRat.lean#L98-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PtsIntegralLogNormRat.lean#L98-L102

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
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionIntegral_pullDeg_add_0293f0b8a195 (κ : K → K') (a b : K → ℤ) : pullDeg κ (a + b) = pullDeg κ a + pullDeg κ b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ArithmeticIntersectionIntegral».«pullDeg_add» := P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionIntegral_pullDeg_add_0293f0b8a195
