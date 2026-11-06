-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitBitstringEquiv_symm_at
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerQubitBitstringEquiv_symm_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:41:38.23182+00:00
-- url     : https://prove2.me/theorems/e669fc58-2753-4940-856b-468c154db957
-- title:
--   Finite Instrument: tensor Power Qubit Bitstring Equiv symm at
-- statement:
--   Reading a coordinate of an inverse-flattened history returns the literal
--   bit stored at that flattened trial/site coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Registers/Marginal.lean#L316-L325
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Registers/Marginal.lean#L316-L325

import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalChannel
import Definitions.Def_QEC_Semantics_Instruments_Registers_Marginal
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerQubitBitstringEquiv_symm_at
    (iota : Type u) [Fintype iota] (attempts : Nat)
    (bits : Qubit.Bitstring (Fin attempts × iota))
    (trial : Fin attempts) (site : iota) :
    tensorPowerHistoryAt (Qubit.Bitstring iota) attempts
        ((tensorPowerQubitBitstringEquiv iota attempts).symm bits) trial site =
      bits (trial, site) := by sorry
