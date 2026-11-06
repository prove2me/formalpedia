-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_vonNeumannEntropy_abc_le_c_of_conditional_substitutions
-- name    : QEC.Bounds.BPTEntropy.vonNeumannEntropy_abc_le_c_of_conditional_substitutions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:48:05.032936+00:00
-- url     : https://prove2.me/theorems/2d03b85c-ecb7-488e-8f3a-d2a1c837c49f
-- title:
--   BPTEntropy: von Neumann Entropy abc le c of conditional substitutions
-- statement:
--   The exact `A`/`B`/`C` entropy calculation in the BPT argument.  The two
--   equalities are the separately derived correctability substitutions for `A`
--   and `B`; the proof below supplies precisely the two subadditivity inequalities
--   and their sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L411-L429
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L411-L429

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

theorem QEC.Bounds.BPTEntropy.vonNeumannEntropy_abc_le_c_of_conditional_substitutions
    (A B C : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [FiniteQuantumSystem C]
    (rho : DensityOperator (CompositeSystem A (CompositeSystem B C)))
    (hA : rho.vonNeumannEntropy - (leftMarginal rho).vonNeumannEntropy =
      - (rightMarginal rho).vonNeumannEntropy)
    (hB : rho.vonNeumannEntropy -
        (leftMarginal ((abcToBac A B C).conjDensity rho)).vonNeumannEntropy =
      - (rightMarginal ((abcToBac A B C).conjDensity rho)).vonNeumannEntropy) :
    rho.vonNeumannEntropy <= (leftMarginal (leftMarginal rho)).vonNeumannEntropy := by sorry
