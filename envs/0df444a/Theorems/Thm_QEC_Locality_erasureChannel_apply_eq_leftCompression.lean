-- Prove2me | Theorems.Thm_QEC_Locality_erasureChannel_apply_eq_leftCompression
-- name    : QEC.Locality.erasureChannel_apply_eq_leftCompression
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:38:33.035942+00:00
-- url     : https://prove2.me/theorems/ea522692-8d01-4d9d-9949-d4be4695b1da
-- title:
--   Locality: erasure Channel apply eq left Compression
-- statement:
--   The Locality construction uses the erasure Channel apply eq left Compression property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L263-L294
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L263-L294

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

theorem QEC.Locality.erasureChannel_apply_eq_leftCompression (S : FiniteSubsystem ι)
    (A : Operator S.factorizedSystem) :
    S.erasureChannel A = leftCompression S A := by sorry
