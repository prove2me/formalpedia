-- Prove2me | Theorems.Thm_TopkisRation_TimeMono_lemma_6
-- name    : TopkisRation.TimeMono.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:47:47.469695+00:00
-- url     : https://prove2.me/theorems/39f63f72-1ade-4075-8c40-45dde9425afc
-- title:
--   Lemma 6, p. 168 — equal increases of stock and backlog are worth more at lower stock: g_t(z̄,b) − g_t(z,b) ≤ g_t(z̄+1·y, b+y) − g_t(z+1·y, b+y)
-- statement:
--   Consider the $n$-class rationing model with the standing assumptions (A)–(C) and the expected optimal cost $g_t(z,b)$ of the last $t$ intervals. Suppose that $a_i \in \{0,1\}$ for every interval $1 \le i \le t$, where $0 \le t \le k$. Let $0 \le z \le \bar z$ be two **stock levels** (here $\bar z$ is a stock level, not a critical level), $b \ge 0$ a backlog vector and $y \ge 0$ a vector of additional backlogs, and write $\mathbf 1\cdot y = \sum_i y^i$. Then
--   $$
--   g_t(\bar z, b) - g_t(z, b) \le g_t(\bar z + \mathbf 1\cdot y,\, b + y) - g_t(z + \mathbf 1\cdot y,\, b + y).
--   $$
--
--   In the paper's words, the increased flexibility added by an equal increase in the stock level and the total backlog is of more value for lower initial stock levels. It is used in the proof of Lemma 7.
--
--   **Formalization Note.** The paper writes "suppose $a_t$ is 0 or 1 for each $t$"; the hypothesis is required only for $1 \le i \le t$, the intervals $g_t$ depends on.
-- source:
--   Topkis, Optimal ordering and rationing policies in a nonstationary dynamic inventory model with n demand classes, Management Science 15 (1968), p. 168, Lemma 6

import Mathlib
import Definitions.Def_TopkisRation_TimeMono_Model

namespace TopkisRation.TimeMono

theorem lemma_6 {n : ℕ} (M : Model n) (hM : M.Standing) (t : ℕ) (ht : t ≤ M.k)
    (ha : ∀ i ∈ Finset.Icc 1 t, M.a i = 0 ∨ M.a i = 1)
    (z zbar : ℝ) (hz : 0 ≤ z) (hzz : z ≤ zbar) (b y : Fin n → ℝ) (hb : 0 ≤ b) (hy : 0 ≤ y) :
    M.g t zbar b - M.g t z b ≤
      M.g t (zbar + ∑ i, y i) (b + y) - M.g t (z + ∑ i, y i) (b + y) := by sorry

end TopkisRation.TimeMono
