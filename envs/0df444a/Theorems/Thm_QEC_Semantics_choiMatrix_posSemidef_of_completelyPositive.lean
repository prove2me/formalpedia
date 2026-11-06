-- Prove2me | Theorems.Thm_QEC_Semantics_choiMatrix_posSemidef_of_completelyPositive
-- name    : QEC.Semantics.choiMatrix_posSemidef_of_completelyPositive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:56:47.96004+00:00
-- url     : https://prove2.me/theorems/f9ad6fb6-36a0-4684-bd09-2f84ea96ae77
-- title:
--   Semantics: choi Matrix pos Semidef of completely Positive
-- statement:
--   Complete positivity in the project matrix-amplification sense makes the
--   project-local Choi matrix positive semidefinite.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Choi.lean#L174-L186
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Choi.lean#L174-L186

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Channels_Choi
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

theorem QEC.Semantics.choiMatrix_posSemidef_of_completelyPositive {n : Nat} {βK : Type*}
    [Fintype βK]
    (Φ : Operator H →ₗ[Complex] Operator K)
    (hΦ : CompletelyPositive Φ)
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis βK Complex K) :
    (choiMatrix Φ bH bK).PosSemidef := by sorry
