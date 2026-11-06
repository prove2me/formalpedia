-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBranchOperatorMatrixEntryProduct_eq_prod
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerBranchOperatorMatrixEntryProduct_eq_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:55:28.937104+00:00
-- url     : https://prove2.me/theorems/53e66613-dc43-4fe3-8f19-481ed77632a7
-- title:
--   Finite Instrument: tensor Power Branch Operator Matrix Entry Product eq prod
-- statement:
--   The recursive matrix-entry product is equivalently the finite product of
--   the actual trial entries, multiplied by the literal tensor-unit entry.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BranchOperator.lean#L95-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BranchOperator.lean#L95-L125

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_Basis
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
omit [Fintype Ω]

theorem QEC.Semantics.FiniteInstrument.tensorPowerBranchOperatorMatrixEntryProduct_eq_prod
    {β : Type y} [Fintype β] (basis : OrthonormalBasis β Complex K)
    (branch : Ω → Operator K)
    (unit : Operator (tensorPowerCarrier K 0)) :
    ∀ (attempts : Nat) (history : tensorPowerHistory Ω attempts)
      (left right : tensorPowerHistory β attempts),
      tensorPowerBranchOperatorMatrixEntryProduct basis branch unit attempts
          history left right =
        inner Complex (tensorPowerBasis basis 0 PUnit.unit)
            (unit (tensorPowerBasis basis 0 PUnit.unit)) *
          ∏ trial : Fin attempts,
            inner Complex
              (basis (tensorPowerHistoryAt β attempts left trial))
              (branch (tensorPowerHistoryAt Ω attempts history trial)
                (basis (tensorPowerHistoryAt β attempts right trial))) := by sorry
