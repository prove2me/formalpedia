-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_rightMarginal_eq_rightMarginal_leftMarginal_abcToBac
-- name    : QEC.Bounds.BPTEntropy.rightMarginal_eq_rightMarginal_leftMarginal_abcToBac
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:27:22.81624+00:00
-- url     : https://prove2.me/theorems/b4609f2c-cb4f-4cdd-8ef1-4f79f34aee8e
-- title:
--   BPTEntropy: right Marginal eq right Marginal left Marginal abc To Bac
-- statement:
--   The `A` marginal is unchanged by the explicit `A`/`B` reassociation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L320-L331
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L320-L331

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
open QEC.Bounds.BPTEntropy
open Semantics
open Semantics.DensityOperator
universe u

theorem QEC.Bounds.BPTEntropy.rightMarginal_eq_rightMarginal_leftMarginal_abcToBac
    (A B C : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [FiniteQuantumSystem C]
    (rho : DensityOperator (CompositeSystem A (CompositeSystem B C))) :
    rightMarginal rho =
      rightMarginal (leftMarginal ((abcToBac A B C).conjDensity rho)) := by sorry
