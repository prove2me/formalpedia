-- Prove2me | Theorems.Thm_QEC_Bounds_BPT_QuantumCodeParameters_ofCodeParameters_blockLength
-- name    : QEC.Bounds.BPT.QuantumCodeParameters.ofCodeParameters_blockLength
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:09:18.504257+00:00
-- url     : https://prove2.me/theorems/75a5001a-1da4-4688-8687-9918e5b2920f
-- title:
--   Quantum Code Parameters: of Code Parameters block Length
-- statement:
--   The Quantum Code Parameters construction uses the of Code Parameters block Length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Bound.lean#L80-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Bound.lean#L80-L83

import Definitions.Def_QEC_Locality_Core_Definitions
import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Bound
set_option autoImplicit false
open QEC
universe u v w
open QEC.Bounds
open QEC.Bounds.BPT
open QEC.Bounds.BPT.QuantumCodeParameters

theorem QEC.Bounds.BPT.QuantumCodeParameters.ofCodeParameters_blockLength {F : Type u} {ι : Type v} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] (p : Coding.CodeParameters F ι) :
    (ofCodeParameters p).blockLength = (p.length : ℝ) := by sorry

attribute [defeq] QEC.Bounds.BPT.QuantumCodeParameters.ofCodeParameters_blockLength
