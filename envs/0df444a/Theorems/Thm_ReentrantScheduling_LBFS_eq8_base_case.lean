-- Prove2me | Theorems.Thm_ReentrantScheduling_LBFS_eq8_base_case
-- name    : ReentrantScheduling.LBFS.eq8_base_case
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:19.708888+00:00
-- url     : https://prove2.me/theorems/31f4422d-91f5-45b4-9e8b-7a87ce4897a2
-- title:
--   (8), p. 1410 — a part in the last buffer with $x$ parts ahead exits within $(\overline\tau+\tau_l)+(\tau_l/m_{\sigma_l})x$
-- statement:
--   Consider a nonacyclic flow line operated under the last buffer first serve policy (LBFS), and an admissible run. Suppose that at a time $t_0 \ge 0$ a part $\pi$ is in the last buffer $b_l$ and exactly $x$ parts are ahead of it. Then
--
--   $$
--   e(\pi) \le t_0 + (\overline\tau + \tau_l) + \frac{\tau_l}{m_{\sigma_l}}\, x,
--   $$
--
--   where $\overline\tau = \max_j \tau_j$. The term $\overline\tau$ allows for the nonpreemptive discipline, $(x/m_{\sigma_l})\tau_l$ for processing the $x$ parts ahead, and $\tau_l$ for processing $\pi$ itself.
--
--   This is the base case $k = l$ of the induction (10) behind Theorem 2: it shows the induction hypothesis holds for $k = l$ with $c^{(l)}(\varepsilon) = \overline\tau + \tau_l$, since $w^{(l)} = \tau_l/m_{\sigma_l}$.
--
--   **Formalization Note.** The last buffer is Lean index $l-1$. "Parts ahead" are the parts in the system at $t_0$ that precede $\pi$ in line order. No arrival hypothesis is needed.
-- source:
--   Lu & Kumar, Distributed Scheduling Based on Due Dates and Buffer Priorities, IEEE TAC 36(12), 1991, p. 1410, proof of Theorem 2, the case k = l, (7)–(8)

import Mathlib
import Definitions.Def_ReentrantScheduling_LBFS_Model
import Definitions.Def_ReentrantScheduling_LBFS_Constants

namespace ReentrantScheduling.LBFS

/-- Base case (8), p. 1410: under LBFS, a part `π` in the last buffer `b_l` at time `t₀ ≥ 0`
with `x` parts ahead of it exits by `t₀ + (τ̄ + τ_l) + (τ_l / m_{σ_l}) x`. -/
theorem eq8_base_case (L : Line) (R : Run L) (hR : R.Admissible L.lbfsPrio)
    (π : R.Part) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) (hπ : R.inBuffer π L.last t₀)
    (x : ℕ) (hx : (R.ahead π t₀).encard = x) :
    R.exit π ≤ ((t₀ + (L.τbar + L.τ L.last) + (L.τ L.last / (L.m (L.center L.last) : ℝ)) * x : ℝ)
      : WithTop ℝ) := by sorry

end ReentrantScheduling.LBFS
