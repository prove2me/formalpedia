-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_unitary_leadCoordPlane_64ab9545e835
-- name    : P2M_GroundTheory_Heights__Heights_exists_unitary_leadCoordPlane_64ab9545e835
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:46:52.419377+00:00
-- url     : https://prove2.me/theorems/b05f21c1-083a-4793-a7b1-6d35da6aae21
-- title:
--   P2 M Ground Theory Heights  Heights exists unitary lead Coord Plane 64ab9545e835: P2 M Ground Theory Heights  Heights exists unitary lead Coord Plane 64ab9545e835
-- statement:
--   The P2 M Ground Theory Heights  Heights exists unitary lead Coord Plane 64ab9545e835 construction uses the P2 M Ground Theory Heights  Heights exists unitary lead Coord Plane 64ab9545e835 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentGaussInvariant.lean#L111-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentGaussInvariant.lean#L111-L190

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentGaussInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTangentGaussInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Module
open scoped Matrix
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_exists_unitary_leadCoordPlane_64ab9545e835 {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (T : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (hT : finrank ℂ T = m)
    (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ T) :
    ∃ U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n),
      (∀ v ∈ leadCoordPlane n m, U v ∈ T) ∧ (∀ t ∈ T, ∃ v ∈ leadCoordPlane n m, U v = t) ∧
        U ((‖y‖ : ℂ) • firstCoordVec n) = y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_unitary_leadCoordPlane» := P2M_GroundTheory_Heights__Heights_exists_unitary_leadCoordPlane_64ab9545e835
