-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_unitary_apply_eq_sum_91eb8adc78bc
-- name    : P2M_GroundTheory_Heights__Heights_unitary_apply_eq_sum_91eb8adc78bc
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:50:54.23626+00:00
-- url     : https://prove2.me/theorems/83bd7500-e531-4f29-83ac-c136404e6c2c
-- title:
--   P2 M Ground Theory Heights  Heights unitary apply eq sum 91eb8adc78bc: P2 M Ground Theory Heights  Heights unitary apply eq sum 91eb8adc78bc
-- statement:
--   The P2 M Ground Theory Heights  Heights unitary apply eq sum 91eb8adc78bc construction uses the P2 M Ground Theory Heights  Heights unitary apply eq sum 91eb8adc78bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentGaussInvariant.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentGaussInvariant.lean#L25-L30

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

theorem P2M_GroundTheory_Heights__Heights_unitary_apply_eq_sum_91eb8adc78bc {n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
    (v : EuclideanSpace ℂ (Fin n)) (k : Fin n) : U v k = ∑ j, unitMat U k j * v j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«unitary_apply_eq_sum» := P2M_GroundTheory_Heights__Heights_unitary_apply_eq_sum_91eb8adc78bc
