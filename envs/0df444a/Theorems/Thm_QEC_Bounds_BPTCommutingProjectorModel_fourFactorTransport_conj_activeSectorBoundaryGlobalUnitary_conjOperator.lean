-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_conj_activeSectorBoundaryGlobalUnitary_conjOperator
-- name    : QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_activeSectorBoundaryGlobalUnitary_conjOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:26:04.756712+00:00
-- url     : https://prove2.me/theorems/5524de73-cb4a-4127-b61b-af7c5478d0d3
-- title:
--   BPTCommuting Projector Model: four Factor Transport conj active Sector Boundary Global Unitary conj Operator
-- statement:
--   The physical boundary unitary and the canonical four-factor BC unitary have
--   the same conjugation action after four-factor transport.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/ActiveTransport.lean#L248-L275
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/ActiveTransport.lean#L248-L275

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

theorem QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_activeSectorBoundaryGlobalUnitary_conjOperator
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
      (Semantics.CompositeSystem NB WC))
    (P : Semantics.Operator L.Register) :
    (M.fourFactorTransport region).conjOperator
        ((M.activeSectorBoundaryGlobalUnitary region pB pC UB UC U).conjOperator P) =
      (fourFactorBCUnitaryTransport (A := M.fourFactorA region)
        (D := M.fourFactorD region)
        (activeSectorPhysicalUnitary pB pC UB UC U)).conjOperator
          ((M.fourFactorTransport region).conjOperator P) := by sorry
