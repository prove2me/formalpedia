-- Prove2me | Theorems.Thm_ReentrantScheduling_LBFS_eq10_remaining_delay
-- name    : ReentrantScheduling.LBFS.eq10_remaining_delay
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:08.310174+00:00
-- url     : https://prove2.me/theorems/7d1e92a9-9020-4679-b975-6f3d548a94d1
-- title:
--   (10), pp. 1410–1411 — a part in $B^{(k)}$ with $x$ parts ahead exits within $c^{(k)}(\varepsilon)+(w^{(k)}+\varepsilon)x$
-- statement:
--   Consider an LBFS-admissible run of a nonacyclic flow line, and a buffer index $k \in \{1, \dots, l\}$. Suppose that at a time $t_0 \ge 0$ a part $\pi$ is in the truncated system $B^{(k)} = \{b_k, \dots, b_l\}$ and exactly $x$ parts are ahead of it. Then for every $\varepsilon > 0$
--
--   $$
--   e(\pi) \le t_0 + c^{(k)}(\varepsilon) + \big(w^{(k)} + \varepsilon\big)\, x,
--   $$
--
--   where $w^{(k)}$ is the maximum work per machine (6) brought to a center by a part in $b_k$, ignoring buffers $b_1, \dots, b_{k-1}$, and $c^{(k)}(\varepsilon)$ is the explicit constant defined by (8)–(9).
--
--   This is the induction hypothesis of the proof of Theorem 2, established for every $k$ with the constants of (8)–(9). At $k = 1$ it gives Theorem 2.
--
--   **Formalization Note.** Buffers are 0-based: Lean `k` is the paper's $b_{k+1}$, `L.wk k` is $w^{(k+1)}$ and `L.c k ε` is $c^{(k+1)}(\varepsilon)$. The constant is the explicit recursion, not an existential, so it cannot depend on the run. No arrival hypothesis is needed.
-- source:
--   Lu & Kumar, Distributed Scheduling Based on Due Dates and Buffer Priorities, IEEE TAC 36(12), 1991, pp. 1410–1411, proof of Theorem 2, the induction hypothesis and (10), with c^(k)(ε) of (8)–(9)

import Mathlib
import Definitions.Def_ReentrantScheduling_LBFS_Model
import Definitions.Def_ReentrantScheduling_LBFS_Constants

namespace ReentrantScheduling.LBFS

/-- The induction claim (10), pp. 1410–1411, for every `k`: under LBFS, if at time `t₀ ≥ 0`
part `π` is in `B^(k)` with `x` parts ahead of it, then for every `ε > 0` it exits by
`t₀ + c^(k)(ε) + (w^(k) + ε) x`, with `c^(k)` the explicit constant of (8)–(9). -/
theorem eq10_remaining_delay (L : Line) (R : Run L) (hR : R.Admissible L.lbfsPrio)
    (k : Fin L.l) (ε : ℝ) (hε : 0 < ε) (π : R.Part) (t₀ : ℝ) (ht₀ : 0 ≤ t₀)
    (hπ : R.inBlock π k t₀) (x : ℕ) (hx : (R.ahead π t₀).encard = x) :
    R.exit π ≤ ((t₀ + L.c k ε + (L.wk k + ε) * x : ℝ) : WithTop ℝ) := by sorry

end ReentrantScheduling.LBFS
