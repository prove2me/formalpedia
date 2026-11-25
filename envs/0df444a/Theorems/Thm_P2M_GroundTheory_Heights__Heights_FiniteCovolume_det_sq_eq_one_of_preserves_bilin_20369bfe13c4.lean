-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_det_sq_eq_one_of_preserves_bilin_20369bfe13c4
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_det_sq_eq_one_of_preserves_bilin_20369bfe13c4
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:18:00.833946+00:00
-- url     : https://prove2.me/theorems/0565d68f-4fcd-40fe-89ce-922f265b4860
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume det sq eq one of preserves bilin 20369bfe13c4: P2 M Ground Theory Heights  Heights Finite Covolume det sq eq one of preserves bilin 20369bfe13c4
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume det sq eq one of preserves bilin 20369bfe13c4 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume det sq eq one of preserves bilin 20369bfe13c4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusHaar.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusHaar.lean#L8-L11

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetSqEqOneOfPreservesBilin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusHaar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory Module

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_det_sq_eq_one_of_preserves_bilin_20369bfe13c4 {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (f : V →ₗ[ℝ] V) (hf : ∀ x y, B (f x) (f y) = B x y) : LinearMap.det f ^ 2 = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«det_sq_eq_one_of_preserves_bilin» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_det_sq_eq_one_of_preserves_bilin_20369bfe13c4
