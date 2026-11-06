-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_conj_activeSectorBoundaryGlobalUnitary
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_activeSectorBoundaryGlobalUnitary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T14:24:35.81997+00:00
-- url     : https://prove2.me/theorems/ef92ec1b-9460-435c-8d6e-51434e756ad0
-- title:
--   BPTCommuting Projector Model: four Factor Transport conj active Sector Boundary Global Unitary
-- statement:
--   In canonical four-factor coordinates, the physical global lift is exactly the
--   corresponding active `B tensor C` unitary with identities on `A` and `D`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1775-L1798
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L1775-L1798

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

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_activeSectorBoundaryGlobalUnitary
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
    (M.fourFactorTransport region).conjOperator
      (M.activeSectorBoundaryGlobalUnitary region SB SC UB UC U).toLinearEquiv.toLinearMap =
      M.fourFactorExtendBC region
        (activeSectorPhysicalUnitary SB SC UB UC U).toLinearEquiv.toLinearMap := by sorry
