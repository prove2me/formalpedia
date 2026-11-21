-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cell0Check_ok
-- name    : RandomSizeStable.Stability.RankCutCert.cell0Check_ok
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T17:26:51.300679+00:00
-- url     : https://prove2.me/theorems/39866a1c-35d6-418c-a2c5-028f67b9fc86
-- title:
--   Rank-cut certificate at D* — soundness of the checker for cells near p = 0
-- statement:
--   For every cell data `cd`, if `cell0Check cd = true` then `CellOK` holds on the cell's $p$-interval with the cell's multipliers (as in `cellCheck_ok`). Here `toR z` is $z/2^{64}$ for a pair-of-naturals integer $z$, `qR q` is the rational $q$ as a real, and the cell's $p$-interval is $[$`toR (pm - ph)`, `toR (pm + ph)`$]$. Case $A = 1$ is checked as for interior cells; case 2 is checked after dividing by $p$, using that `tail j a - tail j A` is nonnegative.
-- source:
--   Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission 1342 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1342.pdf), soundness of the certificate checker (not from the paper).

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankCutCert
import Definitions.Def_RandomSizeStable_Stability_RankCutCertEngine

set_option autoImplicit false

open RandomSizeStable.Stability.RankCutCert RandomSizeStable.Stability.RankCutCert.Dev

theorem RandomSizeStable.Stability.RankCutCert.cell0Check_ok (cd : CellData) (h : cell0Check cd = true) :
    CellOK (toR (zsub cd.pm cd.ph)) (toR (zadd cd.pm cd.ph)) (qR cd.l0) (qR cd.l1) (qR cd.l2)
      (fun j => qR (cd.t0 j)) (fun j => qR (cd.t1 j)) := by
  sorry
