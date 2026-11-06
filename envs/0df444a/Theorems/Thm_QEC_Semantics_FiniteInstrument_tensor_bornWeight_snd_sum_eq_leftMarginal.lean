-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensor_bornWeight_snd_sum_eq_leftMarginal
-- name    : QEC.Semantics.FiniteInstrument.tensor_bornWeight_snd_sum_eq_leftMarginal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:20:54.625207+00:00
-- url     : https://prove2.me/theorems/8da4bd56-4f18-4aaf-8f53-686247aa28bf
-- title:
--   Finite Instrument: tensor born Weight snd sum eq left Marginal
-- statement:
--   Summing every visible left-factor outcome of a tensor instrument gives
--   the right visible Born mass on the true left-partial-trace marginal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Tensor/MarginalBornMass.lean#L283-L322
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Tensor/MarginalBornMass.lean#L283-L322

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalBornMass
set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {kappaTwo : Type x} [Fintype kappaTwo]
variable {Xi : Type y} [Fintype Xi]
variable {H K R S : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
variable [NormedAddCommGroup S] [InnerProductSpace Complex S] [FiniteQuantumSystem S]

theorem QEC.Semantics.FiniteInstrument.tensor_bornWeight_snd_sum_eq_leftMarginal
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete)
    (J : FiniteInstrument kappaTwo Xi R S)
    (rightOutcome : Xi) (rho : DensityOperator (CompositeSystem H R)) :
    (∑ leftOutcome : Omega,
      (I.tensor J).bornWeight (leftOutcome, rightOutcome) rho) =
      J.bornWeight rightOutcome (DensityOperator.leftMarginal rho) := by sorry
