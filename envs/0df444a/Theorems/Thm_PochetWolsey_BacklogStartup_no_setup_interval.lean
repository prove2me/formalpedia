-- Prove2me | Theorems.Thm_PochetWolsey_BacklogStartup_no_setup_interval
-- name    : PochetWolsey.BacklogStartup.no_setup_interval
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:31:46.16798+00:00
-- url     : https://prove2.me/theorems/f35f127b-6dbe-4ce8-9c9c-4f5bb57a0f9e
-- title:
--   Observation 10.3 — detecting an interval with no setups
-- statement:
--   Let $y,z$ be an exact binary setup and start-up plan satisfying (10.5)–(10.8), with given $y_0\in\{0,1\}$. For periods $1\le k<t\le n$,
--   $$y_k+\sum_{j=k+1}^t z_j=0\quad\Longleftrightarrow\quad y_k=y_{k+1}=\cdots=y_t=0.$$
--   Thus an initial setup and the subsequent start-ups together detect whether any setup occurs in the interval. This observation underlies the stock inequalities used in the joint formulation.
--
--   Initial-state convention: the parameter `y0` is the same fixed binary datum in every feasible set in this item (printed p. 138 / PDF 155); it is not optimized.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 321 (PDF 334), Observation 10.3

import Mathlib
import Definitions.Def_PochetWolsey_BacklogStartup_StartupModel

namespace PochetWolsey.BacklogStartup

theorem no_setup_interval {n : ℕ} (y0 : ℝ) (hy0 : y0 = 0 ∨ y0 = 1) (y z : Fin n → ℝ) (h : ExactStartup y0 y z)
    (k t : ℕ) (hk : 1 ≤ k) (hkt : k < t) (ht : t ≤ n) :
    (period y k + ∑ j ∈ Finset.Icc (k + 1) t, period z j) = 0 ↔
      ∀ j ∈ Finset.Icc k t, period y j = 0 := by sorry

end PochetWolsey.BacklogStartup
