-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerRegisterProductDensity_matrixEntry
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerRegisterProductDensity_matrixEntry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:08:16.917064+00:00
-- url     : https://prove2.me/theorems/1e1ac0a7-3ce8-404e-8782-954265f222cf
-- title:
--   Finite Instrument: tensor Power Register Product Density matrix Entry
-- statement:
--   Computational entries of the flattened product density are the products
--   of the corresponding local density entries.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Registers/ProductDensity.lean#L106-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Registers/ProductDensity.lean#L106-L179

import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedBranchOperator
import Definitions.Def_QEC_Semantics_Instruments_Registers_ProductDensity
set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerRegisterProductDensity_matrixEntry
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (rho : DensityOperator (Qubit.QubitRegister ι))
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (Qubit.QubitRegister ι) 0))
    (attempts : Nat)
    (left right : Qubit.Bitstring (Fin attempts × ι)) :
    inner Complex
        (EuclideanSpace.basisFun (Qubit.Bitstring (Fin attempts × ι)) Complex left)
        ((tensorPowerRegisterProductDensity ι rho rhoUnit attempts).toOperator
          (EuclideanSpace.basisFun (Qubit.Bitstring (Fin attempts × ι)) Complex
            right)) =
      ∏ trial : Fin attempts,
        inner Complex
          (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex
            (fun port => left (trial, port)))
          (rho.toOperator
            (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex
              (fun port => right (trial, port)))) := by sorry
