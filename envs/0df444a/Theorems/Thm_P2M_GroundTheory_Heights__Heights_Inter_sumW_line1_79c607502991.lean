-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_sumW_line1_79c607502991
-- name    : P2M_GroundTheory_Heights__Heights_Inter_sumW_line1_79c607502991
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:32.864866+00:00
-- url     : https://prove2.me/theorems/57c14213-4614-4477-9258-67c2f4193209
-- title:
--   P2 M Ground Theory Heights  Heights Inter sum W line1 79c607502991: P2 M Ground Theory Heights  Heights Inter sum W line1 79c607502991
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter sum W line1 79c607502991 construction uses the P2 M Ground Theory Heights  Heights Inter sum W line1 79c607502991 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L631-L634
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L631-L634

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

theorem P2M_GroundTheory_Heights__Heights_Inter_sumW_line1_79c607502991 (f : ExW .line1 → ℝ) : ∑ i, f i = f (Sum.inl ()) + f (Sum.inr ()) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«sumW_line1» := P2M_GroundTheory_Heights__Heights_Inter_sumW_line1_79c607502991
