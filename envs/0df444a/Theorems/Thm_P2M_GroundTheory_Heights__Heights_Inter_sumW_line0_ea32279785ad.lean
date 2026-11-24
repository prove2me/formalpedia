-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_sumW_line0_ea32279785ad
-- name    : P2M_GroundTheory_Heights__Heights_Inter_sumW_line0_ea32279785ad
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:04.370818+00:00
-- url     : https://prove2.me/theorems/2a982dd8-4f8c-49a4-a86d-3faf88fe916d
-- title:
--   P2 M Ground Theory Heights  Heights Inter sum W line0 ea32279785ad: P2 M Ground Theory Heights  Heights Inter sum W line0 ea32279785ad
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter sum W line0 ea32279785ad construction uses the P2 M Ground Theory Heights  Heights Inter sum W line0 ea32279785ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L626-L629
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L626-L629

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

theorem P2M_GroundTheory_Heights__Heights_Inter_sumW_line0_ea32279785ad (f : ExW .line0 → ℝ) : ∑ i, f i = f (Sum.inl ()) + f (Sum.inr ()) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«sumW_line0» := P2M_GroundTheory_Heights__Heights_Inter_sumW_line0_ea32279785ad
