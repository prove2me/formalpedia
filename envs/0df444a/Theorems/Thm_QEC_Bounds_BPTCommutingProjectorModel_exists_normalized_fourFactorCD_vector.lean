-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_exists_normalized_fourFactorCD_vector
-- name    : QEC.Bounds.BPTCommutingProjectorModel.exists_normalized_fourFactorCD_vector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:21:33.607233+00:00
-- url     : https://prove2.me/theorems/98f310cb-a2b7-467b-88cb-19ce583beca0
-- title:
--   BPTCommuting Projector Model: exists normalized four Factor CD vector
-- statement:
--   A concrete normalized vector in the second-cut exterior `C tensor D` factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L357-L375
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Sectors/Selection.lean#L357-L375

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.exists_normalized_fourFactorCD_vector
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    ∃ eta : Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region),
      ‖eta‖ = 1 := by sorry
