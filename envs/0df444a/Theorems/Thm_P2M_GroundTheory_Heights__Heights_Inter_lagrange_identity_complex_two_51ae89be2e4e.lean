-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_lagrange_identity_complex_two_51ae89be2e4e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_lagrange_identity_complex_two_51ae89be2e4e
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:25:51.091896+00:00
-- url     : https://prove2.me/theorems/23aa7613-38bc-4061-b737-5bafad264eaa
-- title:
--   P2 M Ground Theory Heights  Heights Inter lagrange identity complex two 51ae89be2e4e: P2 M Ground Theory Heights  Heights Inter lagrange identity complex two 51ae89be2e4e
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter lagrange identity complex two 51ae89be2e4e construction uses the P2 M Ground Theory Heights  Heights Inter lagrange identity complex two 51ae89be2e4e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L661-L666
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L661-L666

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

theorem P2M_GroundTheory_Heights__Heights_Inter_lagrange_identity_complex_two_51ae89be2e4e (u0 u1 w0 w1 : ℂ) :
    ‖u0 * w1 - u1 * w0‖ ^ 2 + ‖star u0 * w0 + star u1 * w1‖ ^ 2 =
      (‖u0‖ ^ 2 + ‖u1‖ ^ 2) * (‖w0‖ ^ 2 + ‖w1‖ ^ 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«lagrange_identity_complex_two» := P2M_GroundTheory_Heights__Heights_Inter_lagrange_identity_complex_two_51ae89be2e4e
