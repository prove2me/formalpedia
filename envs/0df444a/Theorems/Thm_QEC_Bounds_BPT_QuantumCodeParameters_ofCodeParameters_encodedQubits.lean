-- Prove2me | Theorems.Thm_QEC_Bounds_BPT_QuantumCodeParameters_ofCodeParameters_encodedQubits
-- name    : QEC.Bounds.BPT.QuantumCodeParameters.ofCodeParameters_encodedQubits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:07:49.69875+00:00
-- url     : https://prove2.me/theorems/feb265d9-0f37-43dc-9f83-814e5d11dae2
-- title:
--   Quantum Code Parameters: of Code Parameters encoded Qubits
-- statement:
--   The Quantum Code Parameters construction uses the of Code Parameters encoded Qubits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Bound.lean#L86-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Bound.lean#L86-L89

import Definitions.Def_QEC_Locality_Core_Definitions
import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Bound
set_option autoImplicit false
open QEC
universe u v w
open QEC.Bounds
open QEC.Bounds.BPT
open QEC.Bounds.BPT.QuantumCodeParameters

theorem QEC.Bounds.BPT.QuantumCodeParameters.ofCodeParameters_encodedQubits {F : Type u} {ι : Type v} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] (p : Coding.CodeParameters F ι) :
    (ofCodeParameters p).encodedQubits = (p.dimension : ℝ) := by sorry

attribute [defeq] QEC.Bounds.BPT.QuantumCodeParameters.ofCodeParameters_encodedQubits
