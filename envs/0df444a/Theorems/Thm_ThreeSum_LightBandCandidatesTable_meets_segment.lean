-- Prove2me | Theorems.Thm_ThreeSum_LightBandCandidatesTable_meets_segment
-- name    : ThreeSum.LightBandCandidatesTable.meets_segment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:27:04.04375+00:00
-- url     : https://prove2.me/theorems/a65da74c-bfec-4d79-b513-eefd3ce30c0f
-- title:
--   Light Band Candidates Table: meets segment
-- statement:
--   The Light Band Candidates Table construction uses the meets segment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandCandidatesTable.lean#L91-L104
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandCandidatesTable.lean#L91-L104

import Definitions.Def_Submission_ThreeSum_LightBandCandidatesRow
import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_LightBandCandidatesTable
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandCandidatesTable
open Light BandCandidateRows
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {src dst m n U : ℕ} {f : ℕ → ℕ → ℕ}

theorem ThreeSum.LightBandCandidatesTable.meets_segment {pMain pRow pCell : ℕ} (mode : Mode)
    (hmain : P[pMain]? = some (body pRow)) (hrow : P[pRow]? = some (LightBandCandidatesRow.body pCell))
    (hcell : P[pCell]? = some (LightBandCandidatesCell.body mode)) (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d + 1 < lim.depth) (hsrc : src + m * n ≤ dst) (hspace : dst + 4 * (m * n) ≤ lim.space)
    (hword : ((U + 10 : ℕ) : ℤ) ≤ lim.word) (hm : m ≤ U) (hn : n ≤ U) (hf : ∀ i < m, ∀ j < n, f i j ≤ U)
    (hread : ∀ i < m, ∀ j < n, μ (src + i * n + j) = (f i j : ℤ)) :
    Meets lim P pMain d [src, dst, m, n] μ (time m n)
      (fun _ ν =>
        Seg ν dst (cells (rect m n (fun i j => make mode i j (f i j)))) ∧ SameOutside μ ν dst (4 * (m * n))) := by sorry
