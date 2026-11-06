-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBranchOperatorProduct_matrixEntry
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerBranchOperatorProduct_matrixEntry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:55:51.61779+00:00
-- url     : https://prove2.me/theorems/e8ad1f49-35da-42b7-ae55-3fab10258a45
-- title:
--   Finite Instrument: tensor Power Branch Operator Product matrix Entry
-- statement:
--   Computational matrix entries of the literal recursively tensorized
--   branch operator factor exactly over its actual tensor factors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BranchOperator.lean#L61-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BranchOperator.lean#L61-L90

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

theorem QEC.Semantics.FiniteInstrument.tensorPowerBranchOperatorProduct_matrixEntry
    {β : Type y} [Fintype β] (basis : OrthonormalBasis β Complex K)
    (branch : Ω → Operator K)
    (unit : Operator (tensorPowerCarrier K 0)) :
    ∀ (attempts : Nat) (history : tensorPowerHistory Ω attempts)
      (left right : tensorPowerHistory β attempts),
      inner Complex (tensorPowerBasis basis attempts left)
          (tensorPowerBranchOperatorProduct branch unit attempts history
            (tensorPowerBasis basis attempts right)) =
        tensorPowerBranchOperatorMatrixEntryProduct basis branch unit attempts
          history left right := by sorry
