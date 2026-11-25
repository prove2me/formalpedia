-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PullbackDegreeCount_sameOrbit_self_09533dc2b7ba
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PullbackDegreeCount_sameOrbit_self_09533dc2b7ba
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:47:31.405135+00:00
-- url     : https://prove2.me/theorems/fe5fa1d3-8716-4d02-9bbe-299273f3c421
-- title:
--   P2 M Ground Theory Heights  Heights Inter Pullback Degree Count same Orbit self 09533dc2b7ba: P2 M Ground Theory Heights  Heights Inter Pullback Degree Count same Orbit self 09533dc2b7ba
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Pullback Degree Count same Orbit self 09533dc2b7ba construction uses the P2 M Ground Theory Heights  Heights Inter Pullback Degree Count same Orbit self 09533dc2b7ba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NormSegreSameOrbit.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NormSegreSameOrbit.lean#L23-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsChartRankAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PtsOver
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NormSegreSameOrbit
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
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.Inter.PullbackDegreeCount
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
omit [Fintype K'] [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_PullbackDegreeCount_sameOrbit_self_09533dc2b7ba (z : (Σ k', ι' k') → ℂ) : SameOrbit z z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PullbackDegreeCount».«sameOrbit_self» := P2M_GroundTheory_Heights__Heights_Inter_PullbackDegreeCount_sameOrbit_self_09533dc2b7ba
