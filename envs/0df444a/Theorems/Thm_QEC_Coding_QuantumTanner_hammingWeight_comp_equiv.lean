-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_hammingWeight_comp_equiv
-- name    : QEC.Coding.QuantumTanner.hammingWeight_comp_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:12:42.512036+00:00
-- url     : https://prove2.me/theorems/ee6f6c9d-3aa0-4a84-9ee2-b8d6d93ddb9d
-- title:
--   Quantum Tanner: hamming Weight comp equiv
-- statement:
--   Hamming weight is unchanged by a bijection of the coordinate set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/RobustnessTransport.lean#L29-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/RobustnessTransport.lean#L29-L35

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_QuantumTanner_RobustnessTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v

theorem QEC.Coding.QuantumTanner.hammingWeight_comp_equiv
    {F : Type u} [Zero F] [DecidableEq F]
    {I J : Type v} [Fintype I] [Fintype J]
    (e : I ≃ J) (x : Word F J) :
    HammingWeight (fun i => x (e i)) = HammingWeight x := by sorry
