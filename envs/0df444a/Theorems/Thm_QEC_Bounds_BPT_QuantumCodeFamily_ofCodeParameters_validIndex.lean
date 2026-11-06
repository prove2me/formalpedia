-- Prove2me | Theorems.Thm_QEC_Bounds_BPT_QuantumCodeFamily_ofCodeParameters_validIndex
-- name    : QEC.Bounds.BPT.QuantumCodeFamily.ofCodeParameters_validIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:08:13.11384+00:00
-- url     : https://prove2.me/theorems/0a16a971-55da-4a3b-a239-f2e98b9ebcbf
-- title:
--   Quantum Code Family: of Code Parameters valid Index
-- statement:
--   The Quantum Code Family construction uses the of Code Parameters valid Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Bound.lean#L181-L186
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Bound.lean#L181-L186

import Definitions.Def_QEC_Locality_Core_Definitions
import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Bound
set_option autoImplicit false
open QEC
universe u v w
open QEC.Bounds
open QEC.Bounds.BPT
open QEC.Bounds.BPT.QuantumCodeFamily

theorem QEC.Bounds.BPT.QuantumCodeFamily.ofCodeParameters_validIndex {F : Type u} {ι : Nat → Type v} [Field F]
    [Fintype F] [DecidableEq F] [∀ n, Fintype (ι n)]
    (codeParameters : ∀ n, Coding.CodeParameters F (ι n)) (validIndex : Nat → Prop)
    (n : Nat) :
    (ofCodeParameters codeParameters validIndex).validIndex n = validIndex n := by sorry

attribute [defeq] QEC.Bounds.BPT.QuantumCodeFamily.ofCodeParameters_validIndex
