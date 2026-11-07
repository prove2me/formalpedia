-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_Data_localRestriction_mem_dualTensorCode_of_mem_middleBoundaryCode_dual
-- name    : QEC.Coding.QuantumTanner.Data.localRestriction_mem_dualTensorCode_of_mem_middleBoundaryCode_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:16:13.048035+00:00
-- url     : https://prove2.me/theorems/6322f357-73f3-498e-811e-5af286aad20b
-- title:
--   Data: local Restriction mem dual Tensor Code of mem middle Boundary Code dual
-- statement:
--   The false-side local view belongs to the sum of the dual row/column codes,
--   not to the primal tensor intersection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L315-L321
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L315-L321

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_CSS_WeightDescent
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDistance
import Definitions.Def_QEC_Coding_QuantumTanner_Distance
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe v
open QEC.Coding.QuantumTanner.Data
variable {G A B Square XBasis ZBasis : Type v}
  [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
  [Fintype XBasis] [Fintype ZBasis]

theorem QEC.Coding.QuantumTanner.Data.localRestriction_mem_dualTensorCode_of_mem_middleBoundaryCode_dual
    (D : Data G A B Square XBasis ZBasis) (x : Word (ZMod 2) Square)
    (hx : x ∈ D.chainComplex.middleBoundaryCode.dual.carrier) (g : G) :
    D.complex.localRestriction (g, false) x ∈
      (dualTensorCode D.codeA.dual D.codeB.dual).carrier := by sorry
