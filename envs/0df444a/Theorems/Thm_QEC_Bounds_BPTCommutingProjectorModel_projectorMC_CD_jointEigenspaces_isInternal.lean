-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorMC_CD_jointEigenspaces_isInternal
-- name    : QEC.Bounds.BPTCommutingProjectorModel.projectorMC_CD_jointEigenspaces_isInternal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:55:47.490206+00:00
-- url     : https://prove2.me/theorems/c859d81b-4efe-431f-97a5-c6cd6607a0bb
-- title:
--   BPTCommuting Projector Model: projector MC CD joint Eigenspaces is Internal
-- statement:
--   Finite-dimensional joint spectral decomposition for BPT's first `MC/CD`
--   commuting-projector cut.  The ensuing interaction-algebra refinement must
--   split the `C` factor inside these joint sectors, exactly as in source lines
--   594-607; this theorem supplies the concrete orthogonal sector decomposition
--   on which that refinement acts.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3178-L3186
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3178-L3186

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

theorem QEC.Bounds.BPTCommutingProjectorModel.projectorMC_CD_jointEigenspaces_isInternal
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    DirectSum.IsInternal (fun eigenvalue : Complex × Complex =>
      Module.End.eigenspace (M.projectorAB region * M.projectorBC region) eigenvalue.2 ⊓
        Module.End.eigenspace (M.projectorCD region) eigenvalue.1) := by sorry
