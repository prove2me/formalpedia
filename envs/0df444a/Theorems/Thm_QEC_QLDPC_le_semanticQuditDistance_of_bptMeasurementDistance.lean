-- Prove2me | Theorems.Thm_QEC_QLDPC_le_semanticQuditDistance_of_bptMeasurementDistance
-- name    : QEC.QLDPC.le_semanticQuditDistance_of_bptMeasurementDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:55:18.527426+00:00
-- url     : https://prove2.me/theorems/9b2ffb28-3dbc-421b-b7a3-335162785269
-- title:
--   QLDPC: le semantic Qudit Distance of bpt Measurement Distance
-- statement:
--   BPT detectability bounds the least failed local-operator region for nontrivial codes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/BPTMeasurementDistance.lean#L20-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QLDPC/BPTMeasurementDistance.lean#L20-L43

import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
import Definitions.Def_QEC_Coding_QLDPC_BPTMeasurementDistance
set_option autoImplicit false
noncomputable section
open QEC
open QEC.QLDPC
universe u

theorem QEC.QLDPC.le_semanticQuditDistance_of_bptMeasurementDistance
    {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (code : Semantics.QuantumCode (Semantics.Qudit.QuditRegister q))
    (d : Nat)
    (hd : Semantics.QuditSubsystem.BPTMeasurementDistance code d)
    (hfull : ¬ Semantics.QuditSubsystem.NoInformationOn code
      (Semantics.QuditSubsystem.fullRegion q)) :
    d ≤ semanticQuditDistance q code := by sorry
