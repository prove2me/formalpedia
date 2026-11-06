-- Prove2me | Theorems.Thm_QEC_Semantics_choiMatrix_ext
-- name    : QEC.Semantics.choiMatrix_ext
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:56:00.123116+00:00
-- url     : https://prove2.me/theorems/0d2cbe1e-40f5-4bc1-93ce-d7e5d57e0d1d
-- title:
--   Semantics: choi Matrix ext
-- statement:
--   The project-local Choi matrix determines an operator-space linear map once
--   finite orthonormal bases are fixed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Choi.lean#L124-L168
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Choi.lean#L124-L168

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

theorem QEC.Semantics.choiMatrix_ext {n : Nat} {βK : Type*} [Fintype βK]
    (Φ Ψ : Operator H →ₗ[Complex] Operator K)
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis βK Complex K)
    (h : choiMatrix Φ bH bK = choiMatrix Ψ bH bK) :
    Φ = Ψ := by sorry
