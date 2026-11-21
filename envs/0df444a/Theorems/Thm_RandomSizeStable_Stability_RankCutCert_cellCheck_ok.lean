-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellCheck_ok
-- name    : RandomSizeStable.Stability.RankCutCert.cellCheck_ok
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T17:27:01.140847+00:00
-- url     : https://prove2.me/theorems/1b6cf448-4b9b-4367-b83e-a5b72f5566b8
-- title:
--   Rank-cut certificate at D* — soundness of the interior-cell checker
-- statement:
--   For every cell data `cd`, if `cellCheck cd = true` then `CellOK` holds on the cell's $p$-interval with the cell's multipliers: $l_0, l_1, l_2$ = `qR cd.l0`, `qR cd.l1`, `qR cd.l2` and $t_{0,j}, t_{1,j}$ = `qR (cd.t0 j)`, `qR (cd.t1 j)`. Here `toR z` is $z/2^{64}$ for a pair-of-naturals integer $z$, `qR q` is the rational $q$ as a real, and the cell's $p$-interval is $[$`toR (pm - ph)`, `toR (pm + ph)`$]$. The checker evaluates first-order Taylor models of $(1-p)\,G$ (times $\mu p - \Phi(p)$ when $l_2 \ne 0$) on the leaves of two subdivision trees.
-- source:
--   Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission 1342 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1342.pdf), soundness of the certificate checker (not from the paper).

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankCutCert
import Definitions.Def_RandomSizeStable_Stability_RankCutCertEngine

set_option autoImplicit false

open RandomSizeStable.Stability.RankCutCert RandomSizeStable.Stability.RankCutCert.Dev

theorem RandomSizeStable.Stability.RankCutCert.cellCheck_ok (cd : CellData) (h : cellCheck cd = true) :
    CellOK (toR (zsub cd.pm cd.ph)) (toR (zadd cd.pm cd.ph)) (qR cd.l0) (qR cd.l1) (qR cd.l2)
      (fun j => qR (cd.t0 j)) (fun j => qR (cd.t1 j)) := by
  sorry
