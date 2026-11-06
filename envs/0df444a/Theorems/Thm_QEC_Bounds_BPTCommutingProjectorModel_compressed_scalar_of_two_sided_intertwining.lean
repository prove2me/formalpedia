-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_compressed_scalar_of_two_sided_intertwining
-- name    : QEC.Bounds.BPTCommutingProjectorModel.compressed_scalar_of_two_sided_intertwining
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:36:08.628738+00:00
-- url     : https://prove2.me/theorems/280d3304-1cbe-4c3e-aa33-8bb1b8ff319b
-- title:
--   BPTCommuting Projector Model: compressed scalar of two sided intertwining
-- statement:
--   Scalar compression descends through a two-sided compressed coordinate block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/ScalarTransport.lean#L96-L130
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/ScalarTransport.lean#L96-L130

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_ProjectionBlock
import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_ScalarTransport
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.compressed_scalar_of_two_sided_intertwining
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (J : H →ₗ[Complex] K) (Jadj : K →ₗ[Complex] H)
    (R L : Semantics.Operator K) (Rsub Lsub : Semantics.Operator H)
    (scalar : Complex)
    (hRleft : Jadj.comp R = Rsub.comp Jadj)
    (hRright : R.comp J = J.comp Rsub)
    (hprobe : Jadj.comp (L.comp J) = Lsub)
    (hRsub : Rsub = Jadj.comp (R.comp J))
    (hscalar : R * L * R = scalar • R) :
    Rsub * Lsub * Rsub = scalar • Rsub := by sorry
