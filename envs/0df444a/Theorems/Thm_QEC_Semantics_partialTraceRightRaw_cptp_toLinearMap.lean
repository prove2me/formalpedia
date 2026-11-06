-- Prove2me | Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
-- name    : QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:47:15.494364+00:00
-- url     : https://prove2.me/theorems/ff7be340-5182-453a-8008-4a2761759939
-- title:
--   Semantics: partial Trace Right Raw cptp to Linear Map
-- statement:
--   The Semantics construction uses the partial Trace Right Raw cptp to Linear Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Core.lean#L318-L322
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Core.lean#L318-L322

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Channels_Core
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct

theorem QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] :
    (partialTraceRightRaw_cptp H K).toLinearMap = partialTraceRightRaw H K := by sorry

attribute [defeq] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
