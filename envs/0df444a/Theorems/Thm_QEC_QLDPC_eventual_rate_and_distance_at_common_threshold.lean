-- Prove2me | Theorems.Thm_QEC_QLDPC_eventual_rate_and_distance_at_common_threshold
-- name    : QEC.QLDPC.eventual_rate_and_distance_at_common_threshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:44:00.33219+00:00
-- url     : https://prove2.me/theorems/a6c378c3-1eb7-4d07-bc2e-8bd1507be024
-- title:
--   QLDPC: eventual rate and distance at common threshold
-- statement:
--   The eventual rate and distance bounds can be used at one common threshold.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/AsymptoticallyGoodFamily.lean#L68-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/AsymptoticallyGoodFamily.lean#L68-L80

import Definitions.Def_QEC_Coding_QLDPC_QuantumCodeFamily
import Definitions.Def_QEC_Coding_QLDPC_AsymptoticallyGoodFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.QLDPC
universe u v w
variable {A : Type u} {ι : A → Type v} {κ : A → Type w}
variable [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)]

theorem QEC.QLDPC.eventual_rate_and_distance_at_common_threshold
    (F : QuantumCodeFamily A ι κ) (rate relativeDistance : ℝ)
    (hRate : HasEventualRateAtLeast F rate)
    (hDistance : HasEventualRelativeDistanceAtLeast F relativeDistance) :
    ∃ N : Nat, ∀ a, N ≤ F.blockLength a →
      rate * (F.blockLength a : ℝ) ≤ (F.encodedDimension a : ℝ) ∧
      relativeDistance * (F.blockLength a : ℝ) ≤ (F.distance a : ℝ) := by sorry
