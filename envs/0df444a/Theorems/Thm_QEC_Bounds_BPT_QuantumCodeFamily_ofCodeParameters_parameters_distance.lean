-- Prove2me | Theorems.Thm_QEC_Bounds_BPT_QuantumCodeFamily_ofCodeParameters_parameters_distance
-- name    : QEC.Bounds.BPT.QuantumCodeFamily.ofCodeParameters_parameters_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:09:30.689727+00:00
-- url     : https://prove2.me/theorems/05f836e3-59ab-4fc5-aa33-dbddb6a0b3a5
-- title:
--   Quantum Code Family: of Code Parameters parameters distance
-- statement:
--   The Quantum Code Family construction uses the of Code Parameters parameters distance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Bound.lean#L207-L213
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Bound.lean#L207-L213

import Definitions.Def_QEC_Locality_Core_Definitions
import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Bound
set_option autoImplicit false
open QEC
universe u v w
open QEC.Bounds
open QEC.Bounds.BPT
open QEC.Bounds.BPT.QuantumCodeFamily

theorem QEC.Bounds.BPT.QuantumCodeFamily.ofCodeParameters_parameters_distance {F : Type u} {ι : Nat → Type v}
    [Field F] [Fintype F] [DecidableEq F] [∀ n, Fintype (ι n)]
    (codeParameters : ∀ n, Coding.CodeParameters F (ι n)) (validIndex : Nat → Prop)
    (n : Nat) :
    ((ofCodeParameters codeParameters validIndex).parameters n).distance =
      ((codeParameters n).minimumDistance : ℝ) := by sorry

attribute [defeq] QEC.Bounds.BPT.QuantumCodeFamily.ofCodeParameters_parameters_distance
