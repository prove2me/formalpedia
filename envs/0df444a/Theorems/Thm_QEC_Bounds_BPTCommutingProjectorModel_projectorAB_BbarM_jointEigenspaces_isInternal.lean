-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorAB_BbarM_jointEigenspaces_isInternal
-- name    : QEC.Bounds.BPTCommutingProjectorModel.projectorAB_BbarM_jointEigenspaces_isInternal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:56:05.901989+00:00
-- url     : https://prove2.me/theorems/9d4edcf8-852b-4efe-9887-2251da83c1cb
-- title:
--   BPTCommuting Projector Model: projector AB Bbar M joint Eigenspaces is Internal
-- statement:
--   Finite-dimensional joint spectral decomposition for BPT's second
--   `AB/B bar(M)` commuting-projector cut.  It is the second source decomposition
--   used before correctability makes the `AB'` factor one-dimensional.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3193-L3201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3193-L3201

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

theorem QEC.Bounds.BPTCommutingProjectorModel.projectorAB_BbarM_jointEigenspaces_isInternal
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    DirectSum.IsInternal (fun eigenvalue : Complex × Complex =>
      Module.End.eigenspace (M.projectorAB region) eigenvalue.2 ⊓
        Module.End.eigenspace (M.projectorBC region * M.projectorCD region) eigenvalue.1) := by sorry
