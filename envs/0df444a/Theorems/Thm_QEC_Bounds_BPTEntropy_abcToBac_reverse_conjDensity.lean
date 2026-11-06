-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_abcToBac_reverse_conjDensity
-- name    : QEC.Bounds.BPTEntropy.abcToBac_reverse_conjDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:27:27.104212+00:00
-- url     : https://prove2.me/theorems/946ba497-ece6-4f1d-8dec-6cd3b1bb06c0
-- title:
--   BPTEntropy: abc To Bac reverse conj Density
-- statement:
--   Swapping `A` and `B` twice restores every finite density operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L285-L317
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L285-L317

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

theorem QEC.Bounds.BPTEntropy.abcToBac_reverse_conjDensity
    (A B C : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [FiniteQuantumSystem C]
    (rho : DensityOperator (CompositeSystem A (CompositeSystem B C))) :
    (abcToBac B A C).conjDensity ((abcToBac A B C).conjDensity rho) = rho := by sorry
