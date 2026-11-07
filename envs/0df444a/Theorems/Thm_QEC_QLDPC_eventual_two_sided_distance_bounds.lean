-- Prove2me | Theorems.Thm_QEC_QLDPC_eventual_two_sided_distance_bounds
-- name    : QEC.QLDPC.eventual_two_sided_distance_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:29:34.881535+00:00
-- url     : https://prove2.me/theorems/4375ecfc-65e2-49a0-81b5-23d29ac9407a
-- title:
--   QLDPC: eventual two sided distance bounds
-- statement:
--   An eventual relative-distance lower bound and the universal distance cap
--   give two-sided estimates beyond one threshold. A positive lower-bound constant
--   therefore supplies both sides of linear distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/AsymptoticallyGoodFamily.lean#L85-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/AsymptoticallyGoodFamily.lean#L85-L93

import Definitions.Def_QEC_Coding_QLDPC_QuantumCodeFamily
import Definitions.Def_QEC_Coding_QLDPC_AsymptoticallyGoodFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.QLDPC
universe u v w
variable {A : Type u} {ι : A → Type v} {κ : A → Type w}
variable [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)]

theorem QEC.QLDPC.eventual_two_sided_distance_bounds
    (F : QuantumCodeFamily A ι κ) (relativeDistance : ℝ)
    (hDistance : HasEventualRelativeDistanceAtLeast F relativeDistance) :
    ∃ N : Nat, ∀ a, N ≤ F.blockLength a →
      relativeDistance * (F.blockLength a : ℝ) ≤ (F.distance a : ℝ) ∧
        (F.distance a : ℝ) ≤ (F.blockLength a : ℝ) := by sorry
