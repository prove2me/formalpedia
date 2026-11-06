-- Prove2me | Theorems.Thm_QEC_Locality_factorizedBasis_apply
-- name    : QEC.Locality.factorizedBasis_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:39:28.438361+00:00
-- url     : https://prove2.me/theorems/10f3eeb1-0e32-41e5-b819-d265e324831b
-- title:
--   Locality: factorized Basis apply
-- statement:
--   The Locality construction uses the factorized Basis apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L350-L354
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L350-L354

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
set_option autoImplicit false
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.factorizedBasis_apply (S : FiniteSubsystem ι)
    (p : Qubit.Bitstring S.SelectedCoordinates × Qubit.Bitstring S.ComplementCoordinates) :
    factorizedBasis S p = ket p.1 ⊗ₜ[Complex] ket p.2 := by sorry
