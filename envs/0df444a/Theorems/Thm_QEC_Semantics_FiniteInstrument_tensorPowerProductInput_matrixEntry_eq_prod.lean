-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerProductInput_matrixEntry_eq_prod
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerProductInput_matrixEntry_eq_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:57:01.829953+00:00
-- url     : https://prove2.me/theorems/6d03b9a2-542a-4fdf-a4ff-f2713329796d
-- title:
--   Finite Instrument: tensor Power Product Input matrix Entry eq prod
-- statement:
--   Computational entries of a recursively tensorized density factor over
--   the actual trial indices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Registers/ProductDensity.lean#L51-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Registers/ProductDensity.lean#L51-L90

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

theorem QEC.Semantics.FiniteInstrument.tensorPowerProductInput_matrixEntry_eq_prod
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
    {β : Type v} [Fintype β]
    (basis : OrthonormalBasis β Complex H)
    (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0)) :
    ∀ (attempts : Nat) (left right : tensorPowerHistory β attempts),
      inner Complex (tensorPowerBasis basis attempts left)
          ((tensorPowerProductInput rho rhoUnit attempts).toOperator
            (tensorPowerBasis basis attempts right)) =
        ∏ trial : Fin attempts,
          inner Complex
            (basis (tensorPowerHistoryAt β attempts left trial))
            (rho.toOperator
              (basis (tensorPowerHistoryAt β attempts right trial))) := by sorry
