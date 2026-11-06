-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_compression_ne_zero_of_reconstruction
-- name    : QEC.Bounds.BPTCommutingProjectorModel.compression_ne_zero_of_reconstruction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:28:30.994199+00:00
-- url     : https://prove2.me/theorems/750d9499-e25f-436e-a82e-cd4030f9e665
-- title:
--   BPTCommuting Projector Model: compression ne zero of reconstruction
-- statement:
--   Nonzeroness reflects across a reconstructed isometric compression.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/LeftProjection.lean#L92-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/LeftProjection.lean#L92-L106

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_Projection
import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_LeftProjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.compression_ne_zero_of_reconstruction
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (J : H →ₗ[Complex] K) (R : Semantics.Operator K) (hR : R ≠ 0)
    (hreconstruct : R = J.comp (((LinearMap.adjoint J).comp (R.comp J)).comp
      (LinearMap.adjoint J))) :
    ((LinearMap.adjoint J).comp (R.comp J)) ≠ 0 := by sorry
