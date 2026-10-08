-- Prove2me | Theorems.Thm_ReentrantScheduling_LBFS_theorem2_contractive_delay
-- name    : ReentrantScheduling.LBFS.theorem2_contractive_delay
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:34.980179+00:00
-- url     : https://prove2.me/theorems/90abfc6d-6ed5-42f0-9f49-203d565fdf7f
-- title:
--   Theorem 2, p. 1410 — under LBFS, $e(\pi)-\alpha(\pi)\le c(\varepsilon)+(\overline w+\varepsilon)x$ (5)
-- statement:
--   **Contractive estimate for the delay under LBFS.** Consider a nonacyclic flow line operated under the last buffer first serve policy, and let $\overline w = \max_\sigma w_\sigma$ be the maximum work brought per machine at a service center by an incoming part, with $w_\sigma$ as in (2). If there are $x$ other parts in the system when a part $\pi$ is released, then for every $\varepsilon > 0$
--
--   $$
--   e(\pi) - \alpha(\pi) \le c(\varepsilon) + (\overline w + \varepsilon)\, x, \qquad (5)
--   $$
--
--   where $c(\varepsilon) = c^{(1)}(\varepsilon)$ is the explicit constant of (8)–(9).
--
--   The estimate is "contractive": the delay grows with the number in the system at a rate $\overline w + \varepsilon$, which is less than $1/\lambda$ under the load condition $\rho = \lambda\overline w < 1$. It is the key step of the stability proof of LBFS (Theorem 3).
--
--   **Formalization Note.** The statement is for every admissible LBFS run and every released part (not one present at time $0$). The $x$ other parts in the system are those released by $\alpha(\pi)$ and not yet exited, including parts released at the same instant. The page's "there exists a constant $c(\varepsilon)$" is instantiated by the constant its proof computes ("From (8) and (9) we can compute $c(\varepsilon) := c^{(1)}(\varepsilon)$", p. 1412). No arrival hypothesis is needed, as on the page.
-- source:
--   Lu & Kumar, Distributed Scheduling Based on Due Dates and Buffer Priorities, IEEE TAC 36(12), 1991, p. 1410, Theorem 2, (5); c(ε) := c^(1)(ε), p. 1412

import Mathlib
import Definitions.Def_ReentrantScheduling_LBFS_Model
import Definitions.Def_ReentrantScheduling_LBFS_Constants

namespace ReentrantScheduling.LBFS

/-- Theorem 2, p. 1410 (5): under LBFS, if there are `x` other parts in the system when a part
`π` is released, then `e(π) − α(π) ≤ c(ε) + (w̄ + ε) x` for every `ε > 0`, with
`c(ε) = c^(1)(ε)`. -/
theorem theorem2_contractive_delay (L : Line) (R : Run L) (hR : R.Admissible L.lbfsPrio)
    (ε : ℝ) (hε : 0 < ε) (π : R.Part) (hπ : ¬ R.initial π)
    (x : ℕ) (hx : (R.othersAtArrival π).encard = x) :
    R.exit π ≤ ((R.α π + L.cLBFS ε + (L.wbar + ε) * x : ℝ) : WithTop ℝ) := by sorry

end ReentrantScheduling.LBFS
