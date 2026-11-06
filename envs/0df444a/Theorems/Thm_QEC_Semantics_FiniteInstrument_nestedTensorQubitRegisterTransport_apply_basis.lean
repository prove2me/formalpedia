-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_nestedTensorQubitRegisterTransport_apply_basis
-- name    : QEC.Semantics.FiniteInstrument.nestedTensorQubitRegisterTransport_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:02:35.852701+00:00
-- url     : https://prove2.me/theorems/64bdfc88-22de-4580-bbe8-9394d0536a7e
-- title:
--   Finite Instrument: nested Tensor Qubit Register Transport apply basis
-- statement:
--   The nested-register transport maps every computational basis vector to
--   the bitstring selected by the flattening equivalence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/NestedTensor/PowerBasis.lean#L131-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/NestedTensor/PowerBasis.lean#L131-L143

import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_Power
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_Basis
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_PowerBasis
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable {beta : Type v} [Fintype beta]

theorem QEC.Semantics.FiniteInstrument.nestedTensorQubitRegisterTransport_apply_basis
    (iota : Type u) [Fintype iota] [DecidableEq iota]
    (branches depth : Nat)
    (history : nestedTensorHistory (Qubit.Bitstring iota) branches depth) :
    nestedTensorQubitRegisterTransport iota branches depth
      (nestedTensorBasis
        (EuclideanSpace.basisFun (Qubit.Bitstring iota) Complex)
        branches depth history) =
      EuclideanSpace.basisFun
        (Qubit.Bitstring (nestedTensorQubitSlots iota branches depth)) Complex
        (nestedTensorQubitBitstringEquiv iota branches depth history) := by sorry
