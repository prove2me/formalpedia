-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBornProduct_eq_prod
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerBornProduct_eq_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:08:12.8339+00:00
-- url     : https://prove2.me/theorems/b66eb60c-5050-42b6-a960-c6e13cdd27c4
-- title:
--   Finite Instrument: tensor Power Born Product eq prod
-- statement:
--   The recursive observed-history Born product is the finite product of its
--   actual trial Born weights.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Registers/ProductDensity.lean#L24-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Registers/ProductDensity.lean#L24-L47

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

theorem QEC.Semantics.FiniteInstrument.tensorPowerBornProduct_eq_prod
    {κ Ω : Type v} [Fintype κ] [Fintype Ω]
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]
    (I : FiniteInstrument κ Ω H K) (rho : DensityOperator H) :
    ∀ (attempts : Nat) (history : tensorPowerHistory Ω attempts),
      tensorPowerBornProduct I rho attempts history =
        ∏ trial : Fin attempts,
          I.bornWeight (tensorPowerHistoryAt Ω attempts history trial) rho := by sorry
