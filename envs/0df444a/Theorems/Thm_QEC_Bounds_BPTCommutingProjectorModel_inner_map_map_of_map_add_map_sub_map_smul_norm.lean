-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_inner_map_map_of_map_add_map_sub_map_smul_norm
-- name    : QEC.Bounds.BPTCommutingProjectorModel.inner_map_map_of_map_add_map_sub_map_smul_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-18T04:17:34.035344+00:00
-- url     : https://prove2.me/theorems/d780aa94-89bf-4fa0-ab76-30976330bcb6
-- title:
--   BPTCommuting Projector Model: inner map map of map add map sub map smul norm
-- statement:
--   Recover inner-product preservation from concrete linearity and norm preservation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L374-L400
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L374-L400

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_Embeddings
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.inner_map_map_of_map_add_map_sub_map_smul_norm
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K]
    (f : H → K)
    (hadd : ∀ x y, f (x + y) = f x + f y)
    (hsub : ∀ x y, f (x - y) = f x - f y)
    (hsmul : ∀ (c : Complex) x, f (c • x) = c • f x)
    (hnorm : ∀ x, ‖f x‖ = ‖x‖)
    (x y : H) : inner Complex (f x) (f y) = inner Complex x y := by sorry
