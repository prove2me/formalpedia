-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_eval_exh_fa7de0d52714
-- name    : P2M_GroundTheory_Heights__Heights_Inter_eval_exh_fa7de0d52714
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:02:21.960037+00:00
-- url     : https://prove2.me/theorems/f2cdbf61-56d7-4e08-83eb-8490abf38b6d
-- title:
--   P2 M Ground Theory Heights  Heights Inter eval exh fa7de0d52714: P2 M Ground Theory Heights  Heights Inter eval exh fa7de0d52714
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter eval exh fa7de0d52714 construction uses the P2 M Ground Theory Heights  Heights Inter eval exh fa7de0d52714 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L716-L717
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L716-L717

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

theorem P2M_GroundTheory_Heights__Heights_Inter_eval_exh_fa7de0d52714 (z : (Σ k, ExW k) → ℂ) : eval z (map (Int.castRingHom ℂ) exh) = z ⟨.base, ()⟩ ^ 3 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«eval_exh» := P2M_GroundTheory_Heights__Heights_Inter_eval_exh_fa7de0d52714
