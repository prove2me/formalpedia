-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_leftMarginal_leftMarginal_eq_leftMarginal_leftMarginal_abcToBac
-- name    : QEC.Bounds.BPTEntropy.leftMarginal_leftMarginal_eq_leftMarginal_leftMarginal_abcToBac
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:27:24.451065+00:00
-- url     : https://prove2.me/theorems/7daf9073-fe7c-42a3-84e8-6dbec1dbf8c7
-- title:
--   BPTEntropy: left Marginal left Marginal eq left Marginal left Marginal abc To Bac
-- statement:
--   The `C` marginal is unchanged by the explicit `A`/`B` reassociation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L334-L403
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L334-L403

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

theorem QEC.Bounds.BPTEntropy.leftMarginal_leftMarginal_eq_leftMarginal_leftMarginal_abcToBac
    (A B C : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [FiniteQuantumSystem C]
    (rho : DensityOperator (CompositeSystem A (CompositeSystem B C))) :
    leftMarginal (leftMarginal rho) =
      leftMarginal (leftMarginal ((abcToBac A B C).conjDensity rho)) := by sorry
