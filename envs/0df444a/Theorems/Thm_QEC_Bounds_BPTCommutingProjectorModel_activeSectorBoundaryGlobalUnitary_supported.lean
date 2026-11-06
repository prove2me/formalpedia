-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_activeSectorBoundaryGlobalUnitary_supported
-- name    : QEC.Bounds.BPTCommutingProjectorModel.activeSectorBoundaryGlobalUnitary_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:52:38.718216+00:00
-- url     : https://prove2.me/theorems/3c5e1936-ba46-4c6f-8e01-47300ceb95f2
-- title:
--   BPTCommuting Projector Model: active Sector Boundary Global Unitary supported
-- statement:
--   The active-sector physical unitary is supported on the physical boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1752-L1769
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1752-L1769

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.activeSectorBoundaryGlobalUnitary_supported
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {WB NB WC NC : Type} [NormedAddCommGroup WB] [InnerProductSpace Complex WB]
    [Semantics.FiniteQuantumSystem WB] [NormedAddCommGroup NB] [InnerProductSpace Complex NB]
    [Semantics.FiniteQuantumSystem NB] [NormedAddCommGroup WC] [InnerProductSpace Complex WC]
    [Semantics.FiniteQuantumSystem WC] [NormedAddCommGroup NC] [InnerProductSpace Complex NC]
    [Semantics.FiniteQuantumSystem NC]
    (SB : Submodule Complex (M.fourFactorB region))
    (SC : Submodule Complex (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport SB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport SC (Semantics.CompositeSystem WC NC))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem NB WC)
      (Semantics.CompositeSystem NB WC)) :
    M.UnitarySupportedOn (M.boundary region)
      (M.activeSectorBoundaryGlobalUnitary region SB SC UB UC U) := by sorry
