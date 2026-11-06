-- Prove2me | Theorems.Thm_QEC_QLDPC_chainComplexCSSRowChecks_qubitCheckDegree_le_incidence
-- name    : QEC.QLDPC.chainComplexCSSRowChecks_qubitCheckDegree_le_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:24:23.308841+00:00
-- url     : https://prove2.me/theorems/55270100-c31a-4b7a-b780-ec4ce185c1bd
-- title:
--   QLDPC: chain Complex CSSRow Checks qubit Check Degree le incidence
-- statement:
--   Deduplicating equal basis-row checks cannot increase any qubit's check degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L636-L658
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/Core.lean#L636-L658

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core
set_option autoImplicit false
open QEC
universe u v w x
open scoped Classical
open QEC.QLDPC

theorem QEC.QLDPC.chainComplexCSSRowChecks_qubitCheckDegree_le_incidence
    {ι κ lambda : Type v} [Fintype ι] [Fintype κ] [Fintype lambda]
    (K : Coding.ChainComplexData
      (ZMod 2) (Coding.Word (ZMod 2) κ) (Coding.Word (ZMod 2) ι)
      (Coding.Word (ZMod 2) lambda)) (q : ι) :
    qubitCheckDegree (chainComplexCSSRowChecks K) q ≤
      ((chainComplexBoundaryIncidence K).variableSupport q).card := by sorry
