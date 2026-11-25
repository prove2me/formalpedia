-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_hermG_one_re_c3c1dc8ca6a2
-- name    : P2M_GroundTheory_Heights__Heights_Inter_hermG_one_re_c3c1dc8ca6a2
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:23:15.218643+00:00
-- url     : https://prove2.me/theorems/4e8814f5-dd32-44ea-ae29-5998012e4ef3
-- title:
--   P2 M Ground Theory Heights  Heights Inter herm G one re c3c1dc8ca6a2: P2 M Ground Theory Heights  Heights Inter herm G one re c3c1dc8ca6a2
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter herm G one re c3c1dc8ca6a2 construction uses the P2 M Ground Theory Heights  Heights Inter herm G one re c3c1dc8ca6a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L672-L677
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L672-L677

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

theorem P2M_GroundTheory_Heights__Heights_Inter_hermG_one_re_c3c1dc8ca6a2 (u : Unit ⊕ Unit → ℂ) :
    (hermG 1 u u).re = ‖u (Sum.inl ())‖ ^ 2 + ‖u (Sum.inr ())‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«hermG_one_re» := P2M_GroundTheory_Heights__Heights_Inter_hermG_one_re_c3c1dc8ca6a2
