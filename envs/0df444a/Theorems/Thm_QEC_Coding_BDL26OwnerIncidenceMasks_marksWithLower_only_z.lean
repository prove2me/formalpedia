-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_marksWithLower_only_z
-- name    : QEC.Coding.BDL26OwnerIncidenceMasks.marksWithLower_only_z
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T09:13:23.921709+00:00
-- url     : https://prove2.me/theorems/10084001-dd2a-4e8e-9097-f1511f5dd880
-- title:
--   BDL26 Owner Incidence Masks: marks With Lower only z
-- statement:
--   The BDL26 Owner Incidence Masks construction uses the marks With Lower only z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryComponentMask.lean#L39-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryComponentMask.lean#L39-L42

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryComponentMask
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26OwnerIncidenceMasks.marksWithLower_only_z (lower : Finset StrictLowerNode) :
    BDL26TopOwnerIsolation.TopMarksAreZ (marksWithLower lower) := by sorry
