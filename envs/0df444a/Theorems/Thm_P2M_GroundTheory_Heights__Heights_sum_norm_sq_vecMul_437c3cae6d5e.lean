-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_sum_norm_sq_vecMul_437c3cae6d5e
-- name    : P2M_GroundTheory_Heights__Heights_sum_norm_sq_vecMul_437c3cae6d5e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:50:45.352502+00:00
-- url     : https://prove2.me/theorems/871bf373-7034-4252-b1ae-20304ff1e8f6
-- title:
--   P2 M Ground Theory Heights  Heights sum norm sq vec Mul 437c3cae6d5e: P2 M Ground Theory Heights  Heights sum norm sq vec Mul 437c3cae6d5e
-- statement:
--   The P2 M Ground Theory Heights  Heights sum norm sq vec Mul 437c3cae6d5e construction uses the P2 M Ground Theory Heights  Heights sum norm sq vec Mul 437c3cae6d5e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentGaussInvariant.lean#L38-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentGaussInvariant.lean#L38-L46

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

theorem P2M_GroundTheory_Heights__Heights_sum_norm_sq_vecMul_437c3cae6d5e {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin n) ℂ) (r : Fin n → ℂ) :
    ∑ j, ‖(r ᵥ* A) j‖ ^ 2 = ∑ j, ‖r j‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«sum_norm_sq_vecMul» := P2M_GroundTheory_Heights__Heights_sum_norm_sq_vecMul_437c3cae6d5e
