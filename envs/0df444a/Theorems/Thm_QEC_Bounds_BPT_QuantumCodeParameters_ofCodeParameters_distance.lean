-- Prove2me | Theorems.Thm_QEC_Bounds_BPT_QuantumCodeParameters_ofCodeParameters_distance
-- name    : QEC.Bounds.BPT.QuantumCodeParameters.ofCodeParameters_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:08:55.938407+00:00
-- url     : https://prove2.me/theorems/06417e09-8ef9-4eba-bebd-4fd7ad041755
-- title:
--   Quantum Code Parameters: of Code Parameters distance
-- statement:
--   The Quantum Code Parameters construction uses the of Code Parameters distance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Bound.lean#L92-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/Bound.lean#L92-L95

import Definitions.Def_QEC_Locality_Core_Definitions
import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Bound
set_option autoImplicit false
open QEC
universe u v w
open QEC.Bounds
open QEC.Bounds.BPT
open QEC.Bounds.BPT.QuantumCodeParameters

theorem QEC.Bounds.BPT.QuantumCodeParameters.ofCodeParameters_distance {F : Type u} {ι : Type v} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] (p : Coding.CodeParameters F ι) :
    (ofCodeParameters p).distance = (p.minimumDistance : ℝ) := by sorry

attribute [defeq] QEC.Bounds.BPT.QuantumCodeParameters.ofCodeParameters_distance
