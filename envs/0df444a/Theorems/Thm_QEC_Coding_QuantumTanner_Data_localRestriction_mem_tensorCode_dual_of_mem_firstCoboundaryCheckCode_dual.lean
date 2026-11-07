-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_Data_localRestriction_mem_tensorCode_dual_of_mem_firstCoboundaryCheckCode_dual
-- name    : QEC.Coding.QuantumTanner.Data.localRestriction_mem_tensorCode_dual_of_mem_firstCoboundaryCheckCode_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:16:32.837292+00:00
-- url     : https://prove2.me/theorems/a0bc76c9-079b-4466-87c2-2b76f2763f34
-- title:
--   Data: local Restriction mem tensor Code dual of mem first Coboundary Check Code dual
-- statement:
--   The symmetric ambient sector satisfies the corresponding true-side
--   constraints, using the tensor of the dual local codes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L302-L311
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L302-L311

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

theorem QEC.Coding.QuantumTanner.Data.localRestriction_mem_tensorCode_dual_of_mem_firstCoboundaryCheckCode_dual
    (D : Data G A B Square XBasis ZBasis) (x : Word (ZMod 2) Square)
    (hx : x ∈ D.chainComplex.firstCoboundaryCheckCode.dual.carrier) (g : G) :
    D.complex.localRestriction (g, true) x ∈
      (tensorCode D.codeA.dual D.codeB.dual).dual.carrier := by sorry
