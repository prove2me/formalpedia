-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_exXi_h_bce7dc8fca97
-- name    : P2M_GroundTheory_Heights__Heights_Inter_exXi_h_bce7dc8fca97
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:01:50.731401+00:00
-- url     : https://prove2.me/theorems/5a95c89d-766b-4b9b-9599-dc712250d7fe
-- title:
--   P2 M Ground Theory Heights  Heights Inter ex Xi h bce7dc8fca97: P2 M Ground Theory Heights  Heights Inter ex Xi h bce7dc8fca97
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter ex Xi h bce7dc8fca97 construction uses the P2 M Ground Theory Heights  Heights Inter ex Xi h bce7dc8fca97 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L648-L659
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L648-L659

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

theorem P2M_GroundTheory_Heights__Heights_Inter_exXi_h_bce7dc8fca97 (w : (Σ k, ExY k) → ℂ) :
    exXi.h w = ‖w ⟨.base, ()⟩‖ ^ 3 * ‖w ⟨.det, ()⟩‖⁻¹ *
      (‖w ⟨.line, Sum.inl ()⟩‖ ^ 2 + ‖w ⟨.line, Sum.inr ()⟩‖ ^ 2)⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«exXi_h» := P2M_GroundTheory_Heights__Heights_Inter_exXi_h_bce7dc8fca97
