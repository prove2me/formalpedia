-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_uniform_topMarks
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.uniform_topMarks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:07:57.601918+00:00
-- url     : https://prove2.me/theorems/b1cb6997-bba0-4964-89ba-30da40639361
-- title:
--   BDL26 Canonical History Marks: uniform top Marks
-- statement:
--   Exact equality with the merged uniform input's original top-output marks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Consistency.lean#L149-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Consistency.lean#L149-L189

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26ReplacementSupport MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26CanonicalHistoryMarks.uniform_topMarks (S : OddScale) (j : Nat) :
    aboveMarks S (2 * j + 2) (BDL26UniformHistoryObstruction.upperSyndrome S j)
      (Fin.last (2 * j + 1)) = BDL26UniformHistoryObstruction.topMarks S j := by sorry
