-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_prod_WBlk_ea7f2fa78cf5
-- name    : P2M_GroundTheory_Heights__Heights_Inter_prod_WBlk_ea7f2fa78cf5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:04.735952+00:00
-- url     : https://prove2.me/theorems/c1c9c74d-009f-4f56-9685-97da4d14ee0f
-- title:
--   P2 M Ground Theory Heights  Heights Inter prod WBlk ea7f2fa78cf5: P2 M Ground Theory Heights  Heights Inter prod WBlk ea7f2fa78cf5
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter prod WBlk ea7f2fa78cf5 construction uses the P2 M Ground Theory Heights  Heights Inter prod WBlk ea7f2fa78cf5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L640-L642
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L640-L642

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

theorem P2M_GroundTheory_Heights__Heights_Inter_prod_WBlk_ea7f2fa78cf5 (f : T.WBlk → ℝ) : ∏ k, f k = f .base * (f .det * (f .line0 * f .line1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«prod_WBlk» := P2M_GroundTheory_Heights__Heights_Inter_prod_WBlk_ea7f2fa78cf5
