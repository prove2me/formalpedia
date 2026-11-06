-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensor_rawBornWeight_snd_sum_eq_leftMarginal
-- name    : QEC.Semantics.FiniteInstrument.tensor_rawBornWeight_snd_sum_eq_leftMarginal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:20:48.788398+00:00
-- url     : https://prove2.me/theorems/dbe5a0c3-189b-48ae-8bc0-2cc370a9f791
-- title:
--   Finite Instrument: tensor raw Born Weight snd sum eq left Marginal
-- statement:
--   Summing the raw branches of a complete instrument on the left tensor
--   factor leaves the right raw branch evaluated on the actual left-partial-trace
--   marginal.  The bipartite input may be correlated.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Tensor/MarginalBornMass.lean#L194-L279
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Tensor/MarginalBornMass.lean#L194-L279

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

theorem QEC.Semantics.FiniteInstrument.tensor_rawBornWeight_snd_sum_eq_leftMarginal
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete)
    (J : FiniteInstrument kappaTwo Xi R S)
    (rightIndex : kappaTwo) (rho : DensityOperator (CompositeSystem H R)) :
    (∑ leftIndex : kappa,
      (I.tensor J).rawBornWeight (leftIndex, rightIndex) rho) =
      J.rawBornWeight rightIndex (DensityOperator.leftMarginal rho) := by sorry
