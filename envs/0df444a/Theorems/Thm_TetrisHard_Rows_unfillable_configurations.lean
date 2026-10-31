-- Prove2me | Theorems.Thm_TetrisHard_Rows_unfillable_configurations
-- name    : TetrisHard.Rows.unfillable_configurations
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T22:56:44.268748+00:00
-- url     : https://prove2.me/theorems/1e58971f-1b74-4254-b0ad-39e5e19080e6
-- title:
--   Lemma 5.9 — All eight unfillable configurations, using the full appendix statement
-- statement:
--   Lemma 5.9 In any reasonable rotation model, any bucket containing any of the following is unfillable: 1. a hole. 2. a spurned notch. 3. a balconied 110-floored notch, 011-floored notch, or 111-floored notch. 4. a balconied unfilled sub-notch rectangle. 5. a balconied (α̸ ≡4 0)-veranda in non-notch rows. 6. a balconied 2-veranda. 7. a balconied flat-bottomed 2/3-ceiling discrepancy. 8. a balconied notch-spanning 2/3-ceiling discrepancy.
--
--   In any admissible reasonable rotation model, a bucket with any one of the eight listed patterns is unfillable by arbitrary finite legal trajectories of LG, LS, square and I pieces before row deletions. All three floor patterns and both discrepancy cases are retained; α≥1 and 1≤β≤3 in discrepancy patterns and 1≤j≤3 in the sub-notch rectangle are unchanged. The full Appendix B statement on page 33 is the source.
--
--   Differences from the source:
--   - encoding: one-based rows and columns → zero-based stored cells and signed integer positions; reason: subtracting one preserves every board cell; sentinels prevent subtraction from creating legal cells below the floor
--   - generalization: buckets of the constructed game → any board of width 6s+3 with the same six-column walls, modulo-six notches, height H=6T+22 for some nonnegative T, and at least three staging rows; reason: the geometric claim allows arbitrary interior occupancy but retains the source top boundary and spawn-above-buckets condition; every constructed bucket before row deletion has this frame
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Lemma 5.9, printed p. 33 = PDF p. 33, https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_Reservoir

namespace TetrisHard.Rows

theorem unfillable_configurations
    (R : Rotation) (hR : R.Admissible) (hReason : Reasonable R)
    (B : Board) (s H : ℕ) (hframe : BucketFrame B s H) (j : Fin s) :
    (HasHole B j.val H ∨ SpurnedNotch B j.val H ∨ FlooredNotch B j.val H ∨
      SubNotchRectangle B j.val H ∨ BadNonNotchVeranda B j.val H ∨ TwoVeranda B j.val H ∨
      FlatDiscrepancy B j.val H ∨ NotchDiscrepancy B j.val H) → Unfillable R B j.val H := by sorry

end TetrisHard.Rows
