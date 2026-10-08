-- Prove2me | Theorems.Thm_ReentrantScheduling_LBFS_eq11_exit_after_just_ahead
-- name    : ReentrantScheduling.LBFS.eq11_exit_after_just_ahead
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:11.89107+00:00
-- url     : https://prove2.me/theorems/ab5f23b6-d568-4ca6-8ee0-e1b102f98216
-- title:
--   (11), p. 1411 — $e(\pi)\le e(\pi')+\sum_{j=k}^l\tau_j+(l-k+1)\overline\tau$ for the part $\pi'$ just ahead of $\pi$ in $B^{(k)}$
-- statement:
--   Consider an LBFS-admissible run of a nonacyclic flow line. Suppose that at a time $t_0 \ge 0$ a part $\pi$ is in the truncated system $B^{(k)} = \{b_k, \dots, b_l\}$, and let $\pi'$ be the part just ahead of $\pi$, i.e. the last, in line order, of the parts ahead of $\pi$ at $t_0$. Then
--
--   $$
--   e(\pi) \le e(\pi') + \Big(\sum_{j=k}^{l} \tau_j\Big) + (l-k+1)\,\overline\tau .
--   $$
--
--   At time $e(\pi')$ the part $\pi$ has the highest priority at all remaining buffers, so it can be delayed at each by at most $\overline\tau$ plus a service time. The estimate is the base step $n = 1$ of the inner induction in the proof of (10).
--
--   **Formalization Note.** With 0-based $k$ (the paper's $b_{k+1}$) the sum runs over Lean indices $j \ge k$ and the count of buffers is $l - k$, computed in $\mathbb R$. "Just ahead" is encoded as: $\pi'$ is ahead of $\pi$ at $t_0$ and no part ahead of $\pi$ comes later than $\pi'$ in line order.
-- source:
--   Lu & Kumar, Distributed Scheduling Based on Due Dates and Buffer Priorities, IEEE TAC 36(12), 1991, p. 1411, proof of Theorem 2, (11)

import Mathlib
import Definitions.Def_ReentrantScheduling_LBFS_Model
import Definitions.Def_ReentrantScheduling_LBFS_Constants

namespace ReentrantScheduling.LBFS

/-- Claim (11), p. 1411: under LBFS, if at time `t₀ ≥ 0` part `π` is in `B^(k)` and `π'` is
the part just ahead of it (the last part ahead of `π` in line order), then
`e(π) ≤ e(π') + Σ_{j ≥ k} τ_j + (l − k) τ̄` (0-based `k`; the paper's `(l − k + 1) τ̄`). -/
theorem eq11_exit_after_just_ahead (L : Line) (R : Run L) (hR : R.Admissible L.lbfsPrio)
    (k : Fin L.l) (π π' : R.Part) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) (hπ : R.inBlock π k t₀)
    (hπ' : π' ∈ R.ahead π t₀) (hjust : ∀ q ∈ R.ahead π t₀, R.ord q ≤ R.ord π') :
    R.exit π ≤ R.exit π' +
      (((∑ j ∈ Finset.univ.filter (fun j : Fin L.l => k ≤ j), L.τ j) +
        ((L.l : ℝ) - (k.val : ℝ)) * L.τbar : ℝ) : WithTop ℝ) := by sorry

end ReentrantScheduling.LBFS
