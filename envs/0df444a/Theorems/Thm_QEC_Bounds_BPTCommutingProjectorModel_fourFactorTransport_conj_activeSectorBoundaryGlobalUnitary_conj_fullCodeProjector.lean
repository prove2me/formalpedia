-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_conj_activeSectorBoundaryGlobalUnitary_conj_fullCodeProjector
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_activeSectorBoundaryGlobalUnitary_conj_fullCodeProjector
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T16:27:10.463288+00:00
-- url     : https://prove2.me/theorems/a5b440c5-6292-4670-b358-e33bf3577280
-- title:
--   BPTCommuting Projector Model: four Factor Transport conj active Sector Boundary Global Unitary conj full Code Projector
-- statement:
--   The preceding physical/global conjugation equality applied to the code projector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/ActiveTransport.lean#L278-L299
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/ActiveTransport.lean#L278-L299

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sector
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_ActiveTransport
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_activeSectorBoundaryGlobalUnitary_conj_fullCodeProjector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {WB NB WC NC : Type} [NormedAddCommGroup WB] [InnerProductSpace Complex WB]
    [Semantics.FiniteQuantumSystem WB] [NormedAddCommGroup NB] [InnerProductSpace Complex NB]
    [Semantics.FiniteQuantumSystem NB] [NormedAddCommGroup WC] [InnerProductSpace Complex WC]
    [Semantics.FiniteQuantumSystem WC] [NormedAddCommGroup NC] [InnerProductSpace Complex NC]
    [Semantics.FiniteQuantumSystem NC]
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport pB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport pC (Semantics.CompositeSystem WC NC))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem NB WC)
      (Semantics.CompositeSystem NB WC)) :
    (M.fourFactorTransport region).conjOperator
        ((M.activeSectorBoundaryGlobalUnitary region pB pC UB UC U).conjOperator
          M.fullCodeProjector) =
      (fourFactorBCUnitaryTransport (A := M.fourFactorA region)
        (D := M.fourFactorD region)
        (activeSectorPhysicalUnitary pB pC UB UC U)).conjOperator
          ((M.fourFactorTransport region).conjOperator M.fullCodeProjector) := by sorry
