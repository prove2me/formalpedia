-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedMinorReindex_rowWeight_equiv
-- name    : ThreeSum.TernaryPairedMinorReindex.rowWeight_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:08:35.527139+00:00
-- url     : https://prove2.me/theorems/06f4f291-17ed-4e84-a4ab-18eebd6844d6
-- title:
--   Ternary Paired Minor Reindex: row Weight equiv
-- statement:
--   The Ternary Paired Minor Reindex construction uses the row Weight equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedMinorReindex.lean#L21-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedMinorReindex.lean#L21-L31

import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Definitions.Def_Submission_ThreeSum_TernaryPairedMinorReindex
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedMinorReindex
open Matrix Finset TernaryPairedPotential
open scoped BigOperators

theorem ThreeSum.TernaryPairedMinorReindex.rowWeight_equiv {ι : Type*} [Fintype ι] {Λ d : ℕ}
    (A : ι→Fin Λ→ℤ) (e : Fin d≃ι) :
    rowWeight A=minorWeight (fun i => A (e i)) := by sorry
