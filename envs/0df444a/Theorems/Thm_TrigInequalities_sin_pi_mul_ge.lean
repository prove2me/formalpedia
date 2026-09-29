-- Prove2me | Theorems.Thm_TrigInequalities_sin_pi_mul_ge
-- name    : TrigInequalities.sin_pi_mul_ge
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T18:02:31.890993+00:00
-- url     : https://prove2.me/theorems/1c6bc167-bfe0-4d35-a5b7-c3926de5cfb0
-- title:
--   A linear lower bound for $\sin(\pi s)$ away from the endpoints
-- statement:
--   **$\sin(\pi s)$ is bounded below linearly on $[\delta, 1-\delta]$.**
--
--   For $0 < \delta \le 1/2$ and $\delta \le s \le 1-\delta$,
--
--   $$\sin(\pi s) \;\ge\; 2\delta .$$
--
--   On $[0,1]$ the function $\sin(\pi s)$ is concave, vanishing at both endpoints and peaking at
--   $s = 1/2$. Concavity means it lies above the chord joining $(0,0)$ to $(1/2, 1)$ on the left
--   half, i.e. $\sin(\pi s) \ge 2s$ there, and symmetrically $\sin(\pi s) \ge 2(1-s)$ on the right
--   half. Since $s \in [\delta, 1-\delta]$ forces $\min(s, 1-s) \ge \delta$, both bounds give
--   $\sin(\pi s) \ge 2\delta$.
--
--   The constant $2$ is sharp: at $\delta = 1/2$ the interval degenerates to $\{1/2\}$ and the
--   bound reads $\sin(\pi/2) \ge 1$, an equality.
--
--   The estimate is exactly the quantitative form of "$s$ stays away from the integers" needed in
--   exponential-sum arguments: the Kusmin–Landau inequality requires $\|1 - e(g(n))\| = 2|\sin(\pi g(n))|$
--   to be bounded below, and this lemma converts the separation hypothesis
--   $\delta \le g(n) \le 1-\delta$ into the bound $\ge 4\delta$.
--
--   **Formalization note.** The hypotheses place $s$ in $[\delta, 1-\delta] \subseteq [0,1]$, where
--   $\sin(\pi s) \ge 0$.
-- source:
--   Elementary; the concavity bound underlying the Kusmin–Landau inequality, cf. Graham & Kolesnik, *van der Corput's Method of Exponential Sums*, §2.1. Lean proof extracted from `Salt/ExpSum/Kusmin.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace TrigInequalities

theorem sin_pi_mul_ge {δ s : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hs1 : δ ≤ s)
    (hs2 : s ≤ 1 - δ) : 2 * δ ≤ Real.sin (Real.pi * s) := by sorry

end TrigInequalities
