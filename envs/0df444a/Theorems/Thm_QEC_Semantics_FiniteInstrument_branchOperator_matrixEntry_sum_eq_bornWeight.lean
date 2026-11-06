-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_matrixEntry_sum_eq_bornWeight
-- name    : QEC.Semantics.FiniteInstrument.branchOperator_matrixEntry_sum_eq_bornWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:56:00.934188+00:00
-- url     : https://prove2.me/theorems/8b3c4dfa-ad1e-4799-add8-ee579c682b95
-- title:
--   Finite Instrument: branch Operator matrix Entry sum eq born Weight
-- statement:
--   The sum of computational diagonal entries of one actual observed branch
--   is its complex Born weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BranchOperator.lean#L129-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BranchOperator.lean#L129-L145

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

theorem QEC.Semantics.FiniteInstrument.branchOperator_matrixEntry_sum_eq_bornWeight
    {β : Type y} [Fintype β] (basis : OrthonormalBasis β Complex K)
    (I : FiniteInstrument κ Ω H K) (outcome : Ω) (rho : DensityOperator H) :
    (∑ index : β,
        inner Complex (basis index)
          (I.branchOperator outcome rho.toOperator (basis index))) =
      (I.bornWeight outcome rho : Complex) := by sorry
