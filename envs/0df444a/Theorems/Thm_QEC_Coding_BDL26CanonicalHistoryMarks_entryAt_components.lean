-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_entryAt_components
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.entryAt_components
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:53:26.341197+00:00
-- url     : https://prove2.me/theorems/c21b7a48-2d9e-4618-b8cf-ba227222d357
-- title:
--   BDL26 Canonical History Marks: entry At components
-- statement:
--   Every above-C2 unique snapshot contains the same ordered correction,
--   support and coboundary lists as the actual physical adapter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Snapshots.lean#L134-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Snapshots.lean#L134-L138

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat)
variable (sigma : Input S n)

theorem QEC.Coding.BDL26CanonicalHistoryMarks.entryAt_components (i : StepIndex n) :
    (entryAt S n sigma i.succ).localComponents =
      (outputAt S n sigma i).localComponents.map (fun f => ⟨i.succ, f⟩) := by sorry
