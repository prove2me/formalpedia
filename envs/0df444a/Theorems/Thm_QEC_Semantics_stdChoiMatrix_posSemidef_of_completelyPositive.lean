-- Prove2me | Theorems.Thm_QEC_Semantics_stdChoiMatrix_posSemidef_of_completelyPositive
-- name    : QEC.Semantics.stdChoiMatrix_posSemidef_of_completelyPositive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:57:16.685408+00:00
-- url     : https://prove2.me/theorems/5258d54d-1765-4e3f-b0af-a197c17c978d
-- title:
--   Semantics: std Choi Matrix pos Semidef of completely Positive
-- statement:
--   Standard-basis Choi positivity from project complete positivity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Choi.lean#L196-L201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Choi.lean#L196-L201

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

theorem QEC.Semantics.stdChoiMatrix_posSemidef_of_completelyPositive
    (Φ : Operator H →ₗ[Complex] Operator K)
    (hΦ : CompletelyPositive Φ) :
    (stdChoiMatrix Φ).PosSemidef := by sorry
