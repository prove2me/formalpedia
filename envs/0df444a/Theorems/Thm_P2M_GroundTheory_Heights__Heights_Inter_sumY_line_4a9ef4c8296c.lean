-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_sumY_line_4a9ef4c8296c
-- name    : P2M_GroundTheory_Heights__Heights_Inter_sumY_line_4a9ef4c8296c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:59.083408+00:00
-- url     : https://prove2.me/theorems/8f4a4569-58f7-40b8-9b53-9f30a9d15ed8
-- title:
--   P2 M Ground Theory Heights  Heights Inter sum Y line 4a9ef4c8296c: P2 M Ground Theory Heights  Heights Inter sum Y line 4a9ef4c8296c
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter sum Y line 4a9ef4c8296c construction uses the P2 M Ground Theory Heights  Heights Inter sum Y line 4a9ef4c8296c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L613-L616
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L613-L616

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

theorem P2M_GroundTheory_Heights__Heights_Inter_sumY_line_4a9ef4c8296c (f : ExY .line → ℝ) : ∑ i, f i = f (Sum.inl ()) + f (Sum.inr ()) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«sumY_line» := P2M_GroundTheory_Heights__Heights_Inter_sumY_line_4a9ef4c8296c
