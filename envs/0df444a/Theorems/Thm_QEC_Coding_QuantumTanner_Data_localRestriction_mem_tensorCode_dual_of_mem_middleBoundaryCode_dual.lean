-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_Data_localRestriction_mem_tensorCode_dual_of_mem_middleBoundaryCode_dual
-- name    : QEC.Coding.QuantumTanner.Data.localRestriction_mem_tensorCode_dual_of_mem_middleBoundaryCode_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:16:10.507663+00:00
-- url     : https://prove2.me/theorems/62acffb8-3576-47e4-91d7-e115f38c9bfe
-- title:
--   Data: local Restriction mem tensor Code dual of mem middle Boundary Code dual
-- statement:
--   Orthogonality to the global Z checks implies orthogonality to the primal
--   local tensor code on the false side, using the actual check subcode.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L290-L298
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L290-L298

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

theorem QEC.Coding.QuantumTanner.Data.localRestriction_mem_tensorCode_dual_of_mem_middleBoundaryCode_dual
    (D : Data G A B Square XBasis ZBasis) (x : Word (ZMod 2) Square)
    (hx : x ∈ D.chainComplex.middleBoundaryCode.dual.carrier) (g : G) :
    D.complex.localRestriction (g, false) x ∈ (tensorCode D.codeA D.codeB).dual.carrier := by sorry
