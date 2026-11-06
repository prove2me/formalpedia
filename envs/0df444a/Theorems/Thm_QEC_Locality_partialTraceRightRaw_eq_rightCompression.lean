-- Prove2me | Theorems.Thm_QEC_Locality_partialTraceRightRaw_eq_rightCompression
-- name    : QEC.Locality.partialTraceRightRaw_eq_rightCompression
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:38:17.940048+00:00
-- url     : https://prove2.me/theorems/403ac351-1189-4bdb-9a96-f8438e72a329
-- title:
--   Locality: partial Trace Right Raw eq right Compression
-- statement:
--   The Locality construction uses the partial Trace Right Raw eq right Compression property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L123-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L123-L144

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
set_option autoImplicit false
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.partialTraceRightRaw_eq_rightCompression (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {β : Type u} [Fintype β] (b : OrthonormalBasis β Complex K) :
    partialTraceRightRaw H K = rightCompression H K b := by sorry
