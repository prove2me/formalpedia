-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_prod_YBlk_e84c3fe06e16
-- name    : P2M_GroundTheory_Heights__Heights_Inter_prod_YBlk_e84c3fe06e16
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:28.403818+00:00
-- url     : https://prove2.me/theorems/3070adb7-b2d1-4518-aec6-e6493e095cb7
-- title:
--   P2 M Ground Theory Heights  Heights Inter prod YBlk e84c3fe06e16: P2 M Ground Theory Heights  Heights Inter prod YBlk e84c3fe06e16
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter prod YBlk e84c3fe06e16 construction uses the P2 M Ground Theory Heights  Heights Inter prod YBlk e84c3fe06e16 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L636-L638
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L636-L638

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

theorem P2M_GroundTheory_Heights__Heights_Inter_prod_YBlk_e84c3fe06e16 (f : T.YBlk → ℝ) : ∏ k, f k = f .base * (f .det * f .line) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«prod_YBlk» := P2M_GroundTheory_Heights__Heights_Inter_prod_YBlk_e84c3fe06e16
