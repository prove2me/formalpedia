-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_disentangled_of_region_and_externalBoundary_recoverable
-- name    : QEC.Bounds.BPTCommutingProjectorModel.disentangled_of_region_and_externalBoundary_recoverable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T06:17:28.703531+00:00
-- url     : https://prove2.me/theorems/74b3b976-b8c5-4805-8011-54aa642fc509
-- title:
--   BPTCommuting Projector Model: disentangled of region and external Boundary recoverable
-- statement:
--   If `region` and its external boundary are erasure recoverable, the physical
--   boundary unitary disentangles the full code projector into a pure region factor
--   and an arbitrary orthogonal projection on the complement.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Bound.lean#L64-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Bound.lean#L64-L79

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyDisentangling
import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_BPTDisentangling_Bound
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.disentangled_of_region_and_externalBoundary_recoverable
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hM : M.RegionErasureRecoverable region)
    (hC : M.RegionErasureRecoverable (M.externalBoundary region)) :
    M.Disentangled region := by sorry
