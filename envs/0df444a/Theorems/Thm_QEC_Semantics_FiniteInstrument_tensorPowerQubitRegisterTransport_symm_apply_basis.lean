-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitRegisterTransport_symm_apply_basis
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerQubitRegisterTransport_symm_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:41:47.212103+00:00
-- url     : https://prove2.me/theorems/f79d9709-27c5-43f5-84ad-999885418585
-- title:
--   Finite Instrument: tensor Power Qubit Register Transport symm apply basis
-- statement:
--   Undoing the standard tensor-power register transport sends a flattened
--   computational basis vector to the recursive tensor basis vector with the
--   exact inverse history label.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Registers/Marginal.lean#L299-L312
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Registers/Marginal.lean#L299-L312

import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalChannel
import Definitions.Def_QEC_Semantics_Instruments_Registers_Marginal
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerQubitRegisterTransport_symm_apply_basis
    (iota : Type u) [Fintype iota] [DecidableEq iota]
    (attempts : Nat) (bits : Qubit.Bitstring (Fin attempts × iota)) :
    (tensorPowerQubitRegisterTransport iota attempts).symm
        (EuclideanSpace.basisFun
          (Qubit.Bitstring (Fin attempts × iota)) Complex bits) =
      tensorPowerBasis
        (EuclideanSpace.basisFun (Qubit.Bitstring iota) Complex) attempts
        ((tensorPowerQubitBitstringEquiv iota attempts).symm bits) := by sorry
