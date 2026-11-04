-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedMinorReindex_paired_rowWeight
-- name    : ThreeSum.TernaryPairedMinorReindex.paired_rowWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:08:32.698759+00:00
-- url     : https://prove2.me/theorems/3ca058fd-368f-404d-bf91-beb446432042
-- title:
--   Ternary Paired Minor Reindex: paired row Weight
-- statement:
--   The Ternary Paired Minor Reindex construction uses the paired row Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedMinorReindex.lean#L33-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedMinorReindex.lean#L33-L36

import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Definitions.Def_Submission_ThreeSum_TernaryPairedMinorReindex
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedMinorReindex
open Matrix Finset TernaryPairedPotential
open scoped BigOperators

theorem ThreeSum.TernaryPairedMinorReindex.paired_rowWeight {K Λ : ℕ} (L R : Fin K→Fin Λ→ℤ) :
    rowWeight (Sum.elim L R)=
      minorWeight (fun i => Sum.elim L R (finSumFinEquiv.symm i)) := by sorry
