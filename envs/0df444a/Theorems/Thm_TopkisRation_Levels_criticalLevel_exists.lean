-- Prove2me | Theorems.Thm_TopkisRation_Levels_criticalLevel_exists
-- name    : TopkisRation.Levels.criticalLevel_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:49:11.22226+00:00
-- url     : https://prove2.me/theorems/3cecdc8c-f708-4afe-a570-eb4adf9feac0
-- title:
--   §1, p. 166 — the critical rationing level z̄_t^j exists and is unique
-- statement:
--   In the model of Topkis (1968, §1) under Assumptions (A)–(C), let $1\le t\le k$ and let $j$ be a demand class. Consider
--
--   $$
--   \varphi_t^j(w)=p_t^jw+h_t(w)+g_{t-1}(w,\,a_tw\delta_j),\qquad w\ge0 .
--   $$
--
--   There is exactly one $\bar z\in[0,+\infty]$ such that either $\bar z=+\infty$ and $\varphi_t^j$ is strictly decreasing on $[0,\infty)$, or $\bar z$ is finite and is the smallest minimizer of $\varphi_t^j$ on $[0,\infty)$.
--
--   This is what makes the paper's instruction "pick $\{\bar z_t^j\}$ such that …" possible: the critical rationing levels of Theorem 1 are well defined.
--
--   **Formalization Note.** The value $+\infty$ is $\top$ in `WithTop ℝ`. The page calls $\varphi_t^j$ convex (which follows from Lemma 2) and, in its first mention, misprints $p_t^jw$ as $p_t^j$.
-- source:
--   Topkis, Optimal ordering and rationing policies in a nonstationary dynamic inventory model with n demand classes, Management Science 15 (1968), p. 166, §1, definition of z̄_t^j

import Mathlib
import Definitions.Def_TopkisRation_Levels_Model

namespace TopkisRation.Levels

theorem criticalLevel_exists {n : ℕ} (M : Model n) (hM : M.Standing) (t : ℕ)
    (ht : t ∈ Finset.Icc 1 M.k) :
    ∀ j : Fin n, ∃! zbar : WithTop ℝ, IsCriticalLevel (M.levelObj t j) zbar := by sorry

end TopkisRation.Levels
