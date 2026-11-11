-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actualHistory_zero_inputs
-- name    : QEC.Coding.BDL26UniformRXTail.actualHistory_zero_inputs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:56:47.167072+00:00
-- url     : https://prove2.me/theorems/9d3f0c5c-1850-4f16-8efd-b2b690a3d029
-- title:
--   BDL26 Uniform RXTail: actual History zero inputs
-- statement:
--   The BDL26 Uniform RXTail construction uses the actual History zero inputs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/StoppedReadout.lean#L24-L30
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/StoppedReadout.lean#L24-L30

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_StoppedReadout
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26UniformRXTail.actualHistory_zero_inputs (S : OddScale) (n : Nat)
    (sigma : (indexedFamily S (n + 2)).Syndrome (TopIndex (n + 2)))
    (hs : sigma.val = 0) :
    ∀ e ∈ actualHistory S n sigma, e.inputSyndrome.2.val = 0 := by sorry
