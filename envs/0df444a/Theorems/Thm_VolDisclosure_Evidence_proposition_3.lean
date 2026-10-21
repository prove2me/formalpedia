-- Prove2me | Theorems.Thm_VolDisclosure_Evidence_proposition_3
-- name    : VolDisclosure.Evidence.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:40:08.384171+00:00
-- url     : https://prove2.me/theorems/cb9453ca-f468-4880-a1d1-e60954573326
-- title:
--   Proposition 3, bullets 1–2, p. 19 — the optimal policies θ, w_nl, w_dl, w_h below and above the first termination threshold v^1
-- statement:
--   Fix parameters satisfying the standing assumptions of §3, an evidence probability $\pi \in [0,1)$, and let $s$ be the firm value. Write $\hat r = r/(1-(1-p)\pi)$ and $v^1 = \hat r\bar v/(1+\hat r)$. For every $v \in (0, \bar v]$ there is an optimal policy at $v$ with $w_{dh} = w_{nh} =: w_h$ such that:
--
--   1. if $v \in (0, v^1]$:
--   $$
--   \theta = \frac{v^1 - v}{v^1},\quad w_{nl} = 0,\quad w_{dl} = v^1,\quad w_h = \min\Big\{\frac{r\bar v}{p}, \bar v\Big\};
--   $$
--   2. if $v \in (v^1, \bar v]$:
--   $$
--   \theta = 0,\quad w_{nl} = v - \hat r(\bar v - v),\quad w_{dl} = v,\quad w_h = \min\Big\{w_{nl} + \frac{r\bar v}{p}, \bar v\Big\}.
--   $$
--
--   The proposition gives the optimal contract in closed form: stochastic termination below $v^1$, and above it a reward $w_{dl} > w_{nl}$ for disclosing bad luck.
--
--   **Formalization Note.** The statement asserts the existence of an optimal policy with these components; the cash payments are left free, since the proposition does not state them (the cash formula (5) of Proposition 2 is not used). Optimal policies need not be unique (for instance, continuation utility above $\bar v$ and cash are interchangeable when $s = s^*$ there); the paper selects one by paying cash whenever indifferent (p. 16). The third bullet (the $n$-period thresholds $v^n$) is not formalized.
-- source:
--   Fu & Trigilia, Voluntary Disclosure, Moral Hazard and Default Risk, working paper (August 28, 2019), p. 19, Proposition 3 (bullets 1–2); proof pp. 40–41; v^1 from p. 41

import Mathlib
import Definitions.Def_VolDisclosure_Evidence_Model

namespace VolDisclosure.Evidence

/-- Proposition 3, bullets 1–2 (p. 19; proof pp. 40–41): at every `v ∈ (0, v̄]` there is an
optimal policy with `w_dh = w_nh =: w_h` and the stated `θ, w_nl, w_dl, w_h`. -/
theorem proposition_3 (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π < 1)
    (s : ℝ → ℝ) (hs : IsValue P π s) (v : ℝ) (hv0 : 0 < v) (hv1 : v ≤ P.vBar) :
    ∃ a : Policy, IsOptimal P π v s a ∧ a.wdh = a.wnh ∧
      (v ≤ P.v1 π →
        a.θ = (P.v1 π - v) / P.v1 π ∧ a.wnl = 0 ∧ a.wdl = P.v1 π ∧
        a.wnh = min (P.r * P.vBar / P.p) P.vBar) ∧
      (P.v1 π < v →
        a.θ = 0 ∧ a.wnl = v - P.rHat π * (P.vBar - v) ∧ a.wdl = v ∧
        a.wnh = min (a.wnl + P.r * P.vBar / P.p) P.vBar) := by sorry

end VolDisclosure.Evidence
