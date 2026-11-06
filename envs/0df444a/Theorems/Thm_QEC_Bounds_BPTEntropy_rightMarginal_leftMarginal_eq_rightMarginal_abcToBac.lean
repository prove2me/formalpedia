-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_rightMarginal_leftMarginal_eq_rightMarginal_abcToBac
-- name    : QEC.Bounds.BPTEntropy.rightMarginal_leftMarginal_eq_rightMarginal_abcToBac
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:48:31.135931+00:00
-- url     : https://prove2.me/theorems/aaae9c5f-1860-49d4-b56c-829486c44a50
-- title:
--   BPTEntropy: right Marginal left Marginal eq right Marginal abc To Bac
-- statement:
--   Tracing `A` and `C` from `A tensor (B tensor C)` agrees with first
--   reassociating to `B tensor (A tensor C)` and tracing the right factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L57-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L57-L107

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

theorem QEC.Bounds.BPTEntropy.rightMarginal_leftMarginal_eq_rightMarginal_abcToBac
    (A B C : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [FiniteQuantumSystem C]
    (rho : DensityOperator (CompositeSystem A (CompositeSystem B C))) :
    rightMarginal (leftMarginal rho) =
      rightMarginal ((abcToBac A B C).conjDensity rho) := by sorry
