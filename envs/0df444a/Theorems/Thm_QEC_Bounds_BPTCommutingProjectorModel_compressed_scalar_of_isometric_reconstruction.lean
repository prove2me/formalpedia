-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_compressed_scalar_of_isometric_reconstruction
-- name    : QEC.Bounds.BPTCommutingProjectorModel.compressed_scalar_of_isometric_reconstruction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T15:05:20.645723+00:00
-- url     : https://prove2.me/theorems/6cdf724d-8a84-4628-af6d-cb179131d448
-- title:
--   BPTCommuting Projector Model: compressed scalar of isometric reconstruction
-- statement:
--   An isometric reconstruction supplies the two intertwining equations needed to
--   compress a scalar relation.  Keeping this algebra generic prevents the BPT
--   coordinate terms from being unfolded while the relation is transported.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/ScalarTransport.lean#L176-L192
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SecondCut/ScalarTransport.lean#L176-L192

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

theorem QEC.Bounds.BPTCommutingProjectorModel.compressed_scalar_of_isometric_reconstruction
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (J : H →ₗ[Complex] K) (R L : Semantics.Operator K)
    (Lsub : Semantics.Operator H) (scalar : Complex)
    (hJadj : (LinearMap.adjoint J).comp J = (1 : Semantics.Operator H))
    (hreconstruct : R = J.comp
      (((LinearMap.adjoint J).comp (R.comp J)).comp (LinearMap.adjoint J)))
    (hprobe : (LinearMap.adjoint J).comp (L.comp J) = Lsub)
    (hscalar : R * L * R = scalar • R) :
    ((LinearMap.adjoint J).comp (R.comp J)) * Lsub *
        ((LinearMap.adjoint J).comp (R.comp J)) =
      scalar • ((LinearMap.adjoint J).comp (R.comp J)) := by sorry
