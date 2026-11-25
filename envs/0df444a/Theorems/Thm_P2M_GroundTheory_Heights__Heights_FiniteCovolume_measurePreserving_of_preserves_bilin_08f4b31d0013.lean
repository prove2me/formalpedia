-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurePreserving_of_preserves_bilin_08f4b31d0013
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurePreserving_of_preserves_bilin_08f4b31d0013
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:17:53.584321+00:00
-- url     : https://prove2.me/theorems/b6680a5c-72ac-4e8b-87f8-224b36d18a12
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume measure Preserving of preserves bilin 08f4b31d0013: P2 M Ground Theory Heights  Heights Finite Covolume measure Preserving of preserves bilin 08f4b3
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume measure Preserving of preserves bilin 08f4b31d0013 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume measure Preserving of preserves bilin 08f4b31d0013 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusHaar.lean#L13-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusHaar.lean#L13-L27

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurePreserving_of_preserves_bilin_08f4b31d0013 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] (μ : Measure V)
    [μ.IsAddHaarMeasure] (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (f : V →ₗ[ℝ] V) (hf : ∀ x y, B (f x) (f y) = B x y) : MeasurePreserving f μ μ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«measurePreserving_of_preserves_bilin» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurePreserving_of_preserves_bilin_08f4b31d0013
