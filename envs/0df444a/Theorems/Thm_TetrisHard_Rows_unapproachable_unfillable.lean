-- Prove2me | Theorems.Thm_TetrisHard_Rows_unapproachable_unfillable
-- name    : TetrisHard.Rows.unapproachable_unfillable
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T22:56:41.72799+00:00
-- url     : https://prove2.me/theorems/74671d12-33aa-4a2b-9e7c-3d84a2daedb7
-- title:
--   Lemma 5.8 — Unapproachable buckets are unfillable
-- statement:
--   Lemma 5.8 An unapproachable bucket is unfillable.
--
--   In an admissible reasonable rotation model, an unapproachable bucket has no filling by any finite number of LG, LS, square or I pieces following actual trajectories. The exact Figure 6 profile, including the first open notch, defines unapproachable independently of fillability.
--
--   Differences from the source:
--   - encoding: one-based rows and columns → zero-based stored cells and signed integer positions; reason: subtracting one preserves every board cell; sentinels prevent subtraction from creating legal cells below the floor
--   - generalization: buckets of the constructed game → any board of width 6s+3 with the same six-column walls, modulo-six notches, height H=6T+22 for some nonnegative T, and at least three staging rows; reason: the geometric claim allows arbitrary interior occupancy but retains the source top boundary and spawn-above-buckets condition; every constructed bucket before row deletion has this frame
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Lemma 5.8, printed p. 13 = PDF p. 13, https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_Reservoir

namespace TetrisHard.Rows

theorem unapproachable_unfillable
    (R : Rotation) (hR : R.Admissible) (hReason : Reasonable R)
    (B : Board) (s H : ℕ) (hframe : BucketFrame B s H) (j : Fin s)
    (hshape : Unapproachable B j.val H) :
    Unfillable R B j.val H := by sorry

end TetrisHard.Rows
