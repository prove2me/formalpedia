-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_hammingWeight_punctureMap_le
-- name    : QEC.Coding.QuantumTanner.hammingWeight_punctureMap_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:49:12.399843+00:00
-- url     : https://prove2.me/theorems/0cead09a-76d9-4ad0-9ea9-5d27c05c3bae
-- title:
--   Quantum Tanner: hamming Weight puncture Map le
-- statement:
--   Removing coordinates does not increase the number of nonzero entries.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ViewAssembly.lean#L22-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ViewAssembly.lean#L22-L32

import Definitions.Def_QEC_Coding_QuantumTanner_TensorPuncture
import Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe v
variable {A B : Type v} [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.hammingWeight_punctureMap_le {ι : Type v} [Fintype ι]
    (removed : Finset ι) (x : Word (ZMod 2) ι) :
    HammingWeight (punctureMap removed x) ≤ HammingWeight x := by sorry
