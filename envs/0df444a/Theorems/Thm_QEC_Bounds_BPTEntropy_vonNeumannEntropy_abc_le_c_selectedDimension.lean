-- Prove2me | Theorems.Thm_QEC_Bounds_BPTEntropy_vonNeumannEntropy_abc_le_c_selectedDimension
-- name    : QEC.Bounds.BPTEntropy.vonNeumannEntropy_abc_le_c_selectedDimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:34:34.220691+00:00
-- url     : https://prove2.me/theorems/aa8dce8d-f395-43df-8d90-97f8c51ed662
-- title:
--   BPTEntropy: von Neumann Entropy abc le c selected Dimension
-- statement:
--   The BPT A/B/C entropy calculation followed by #411's concrete
--   finite-qudit entropy bound on the `C` register.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L889-L905
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Entropy.lean#L889-L905

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

theorem QEC.Bounds.BPTEntropy.vonNeumannEntropy_abc_le_c_selectedDimension
    (A B : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [FiniteQuantumSystem B]
    {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (regionC : QuditSubsystem q)
    (rho : DensityOperator (CompositeSystem A (CompositeSystem B regionC.selectedSystem)))
    (hA : rho.vonNeumannEntropy - (leftMarginal rho).vonNeumannEntropy =
      - (rightMarginal rho).vonNeumannEntropy)
    (hB : rho.vonNeumannEntropy -
        (leftMarginal ((abcToBac A B regionC.selectedSystem).conjDensity rho)).vonNeumannEntropy =
      - (rightMarginal ((abcToBac A B regionC.selectedSystem).conjDensity rho)).vonNeumannEntropy) :
    rho.vonNeumannEntropy <=
      ∑ i ∈ regionC.selected, Real.logb 2 (q i : Real) := by sorry
