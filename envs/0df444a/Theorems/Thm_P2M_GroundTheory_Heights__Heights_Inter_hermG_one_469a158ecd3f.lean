-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_hermG_one_469a158ecd3f
-- name    : P2M_GroundTheory_Heights__Heights_Inter_hermG_one_469a158ecd3f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:05.07786+00:00
-- url     : https://prove2.me/theorems/1f4b505d-b004-4240-9aa4-3a7c77a1feb9
-- title:
--   P2 M Ground Theory Heights  Heights Inter herm G one 469a158ecd3f: P2 M Ground Theory Heights  Heights Inter herm G one 469a158ecd3f
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter herm G one 469a158ecd3f construction uses the P2 M Ground Theory Heights  Heights Inter herm G one 469a158ecd3f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L668-L670
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L668-L670

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_TsgPolyVolPolyCoeffEven
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsAntisym
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial Matrix ComplexOrder ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
attribute [instance] ProjectiveLineBundle.fieldΩ ProjectiveLineBundle.finι ProjectiveLineBundle.finν ProjectiveLineBundle.finκ ProjectiveLineBundle.acgE ProjectiveLineBundle.modE
  ProjectiveLineBundle.fieldΦ ProjectiveLineBundle.algΦ

theorem P2M_GroundTheory_Heights__Heights_Inter_hermG_one_469a158ecd3f (u w : Unit ⊕ Unit → ℂ) :
    hermG 1 u w = star (u (Sum.inl ())) * w (Sum.inl ()) + star (u (Sum.inr ())) * w (Sum.inr ()) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«hermG_one» := P2M_GroundTheory_Heights__Heights_Inter_hermG_one_469a158ecd3f
