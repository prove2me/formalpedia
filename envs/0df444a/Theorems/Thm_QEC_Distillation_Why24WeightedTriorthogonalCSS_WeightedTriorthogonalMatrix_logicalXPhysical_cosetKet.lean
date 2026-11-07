-- Prove2me | Theorems.Thm_QEC_Distillation_Why24WeightedTriorthogonalCSS_WeightedTriorthogonalMatrix_logicalXPhysical_cosetKet
-- name    : QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.logicalXPhysical_cosetKet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:06:55.559672+00:00
-- url     : https://prove2.me/theorems/1347e20a-1796-4ebc-936f-58e24f788e38
-- title:
--   Weighted Triorthogonal Matrix: logical XPhysical coset Ket
-- statement:
--   The physical X representative translates the appropriate normalized coset.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/WeightedTriorthogonalCSS.lean#L1045-L1059
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/WeightedTriorthogonalCSS.lean#L1045-L1059

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Phase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_WeightedTriorthogonalCSS
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Why24WeightedTriorthogonalCSS
open QEC.Coding QEC.Semantics
open scoped BigOperators
open QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix
variable {Logical Stabilizer Site : Type}
variable [Fintype Logical] [DecidableEq Logical]
variable [Fintype Stabilizer] [DecidableEq Stabilizer]
variable [Fintype Site] [DecidableEq Site]

theorem QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.logicalXPhysical_cosetKet
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    (a : Logical) (beta : F1024) (u : Logical → F1024) :
    R.logicalXPhysical a beta (R.cosetKet u) =
      R.cosetKet (u + logicalBasisWord a beta) := by sorry
