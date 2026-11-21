-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellNCheck_ok
-- name    : RandomSizeStable.Stability.RankCutCert.cellNCheck_ok
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T17:26:50.952949+00:00
-- url     : https://prove2.me/theorems/d72955cd-cf44-4b44-8ca6-d69ff2a0aed3
-- title:
--   Rank-cut certificate at D* — soundness of the checker for cells near p = 1
-- statement:
--   For every cell data `cd`, if `cellNCheck cd = true` then `CellOK` holds on the cell's $p$-interval with the cell's multipliers (as in `cellCheck_ok`). Here `toR z` is $z/2^{64}$ for a pair-of-naturals integer $z$, `qR q` is the rational $q$ as a real, and the cell's $p$-interval is $[$`toR (pm - ph)`, `toR (pm + ph)`$]$. The bracket is checked in the form $B/(1-p) = \mu - vQ(a, a+t) - (1-v)Q(A,1)$ with $Q$ the divided difference of $\Phi$.
-- source:
--   Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission 1342 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1342.pdf), soundness of the certificate checker (not from the paper).

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankCutCert
import Definitions.Def_RandomSizeStable_Stability_RankCutCertEngine

set_option autoImplicit false

open RandomSizeStable.Stability.RankCutCert RandomSizeStable.Stability.RankCutCert.Dev

theorem RandomSizeStable.Stability.RankCutCert.cellNCheck_ok (cd : CellData) (h : cellNCheck cd = true) :
    CellOK (toR (zsub cd.pm cd.ph)) (toR (zadd cd.pm cd.ph)) (qR cd.l0) (qR cd.l1) (qR cd.l2)
      (fun j => qR (cd.t0 j)) (fun j => qR (cd.t1 j)) := by
  sorry
