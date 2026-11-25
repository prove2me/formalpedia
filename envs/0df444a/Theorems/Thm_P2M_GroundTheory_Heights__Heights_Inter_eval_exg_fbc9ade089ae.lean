-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_eval_exg_fbc9ade089ae
-- name    : P2M_GroundTheory_Heights__Heights_Inter_eval_exg_fbc9ade089ae
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:24:22.658672+00:00
-- url     : https://prove2.me/theorems/aab580a3-b5af-4409-85f3-ea10dd0dc386
-- title:
--   P2 M Ground Theory Heights  Heights Inter eval exg fbc9ade089ae: P2 M Ground Theory Heights  Heights Inter eval exg fbc9ade089ae
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter eval exg fbc9ade089ae construction uses the P2 M Ground Theory Heights  Heights Inter eval exg fbc9ade089ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L711-L714
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L711-L714

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

theorem P2M_GroundTheory_Heights__Heights_Inter_eval_exg_fbc9ade089ae (z : (Σ k, ExW k) → ℂ) :
    eval z (map (Int.castRingHom ℂ) exg) = z ⟨.det, ()⟩ *
      (z ⟨.line0, Sum.inl ()⟩ * z ⟨.line1, Sum.inr ()⟩ - z ⟨.line0, Sum.inr ()⟩ * z ⟨.line1, Sum.inl ()⟩) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«eval_exg» := P2M_GroundTheory_Heights__Heights_Inter_eval_exg_fbc9ade089ae
