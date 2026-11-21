-- Prove2me | Theorems.Thm_RandomSizeStable_Stability_RankCutCert_p1Check_ok
-- name    : RandomSizeStable.Stability.RankCutCert.p1Check_ok
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T17:26:54.923211+00:00
-- url     : https://prove2.me/theorems/6a478ea7-9630-40eb-b873-746293ae7979
-- title:
--   Rank-cut certificate at D* — soundness of the p = 1 checker
-- statement:
--   For every cell data `cd` and code `tree`, if `p1Check cd tree = true` then every $t_{0,j} + t_{1,j} \ge 0$ and `P1OK` holds for $t_{0,j}, t_{1,j}$ = `qR (cd.t0 j)`, `qR (cd.t1 j)`: for every $j$ and $0 \le a \le 1$, $a + (t_{0,j} + t_{1,j})(\mu - \phi(\rho_j(a))) \le$ `tail j a`.
-- source:
--   Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission 1342 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1342.pdf), soundness of the certificate checker (not from the paper).

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankCutCert
import Definitions.Def_RandomSizeStable_Stability_RankCutCertEngine

set_option autoImplicit false

open RandomSizeStable.Stability.RankCutCert RandomSizeStable.Stability.RankCutCert.Dev

theorem RandomSizeStable.Stability.RankCutCert.p1Check_ok (cd : CellData) (tree : List Nat)
    (h : p1Check cd tree = true) :
    (∀ j, 0 ≤ qR (cd.t0 j) + qR (cd.t1 j)) ∧
      P1OK (fun j => qR (cd.t0 j)) (fun j => qR (cd.t1 j)) := by
  sorry
