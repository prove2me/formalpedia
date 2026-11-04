-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedMinorReindex_minorWeight_rows
-- name    : ThreeSum.TernaryPairedMinorReindex.minorWeight_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:08:18.383201+00:00
-- url     : https://prove2.me/theorems/99e03071-fcb8-477c-8a04-9ffdc09fc5c3
-- title:
--   Ternary Paired Minor Reindex: minor Weight rows
-- statement:
--   The Ternary Paired Minor Reindex construction uses the minor Weight rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedMinorReindex.lean#L8-L19
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedMinorReindex.lean#L8-L19

import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Definitions.Def_Submission_ThreeSum_TernaryPairedMinorReindex
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedMinorReindex
open Matrix Finset TernaryPairedPotential
open scoped BigOperators

theorem ThreeSum.TernaryPairedMinorReindex.minorWeight_rows {d Λ : ℕ} (A : Matrix (Fin d) (Fin Λ) ℤ) (e : Equiv.Perm (Fin d)) :
    minorWeight (fun i => A (e i))=minorWeight A := by sorry
