-- Prove2me | Theorems.Thm_VolDisclosure_Evidence_lemma_1
-- name    : VolDisclosure.Evidence.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:40:12.739451+00:00
-- url     : https://prove2.me/theorems/e55c06c5-6a02-4053-912c-28b03edaf2ca
-- title:
--   Lemma 1, p. 18 — for 0 < v < v̄, every optimal policy has (ICg) and (ICn) binding and (ICb) strict
-- statement:
--   Fix parameters satisfying the standing assumptions of §3 and an evidence probability $\pi \in (0,1)$, and let $s$ be the firm value. Let $0 < v < \bar v$ and let $(\theta, u, w)$ be an optimal policy of problem (S) at $v$, i.e. feasible and attaining $s(v)$. Then
--   $$
--   \begin{aligned}
--   u_{dh} + \tfrac{w_{dh}}{1+r} &= u_{nh} + \tfrac{w_{nh}}{1+r} &&(IC_g \text{ binds}),\\
--   u_{nh} + \tfrac{w_{nh}}{1+r} &= \delta + u_{nl} + \tfrac{w_{nl}}{1+r} &&(IC_n \text{ binds}),\\
--   u_{dl} + \tfrac{w_{dl}}{1+r} &> u_{nl} + \tfrac{w_{nl}}{1+r} &&(IC_b \text{ strict}).
--   \end{aligned}
--   $$
--
--   The lemma identifies the active constraints from which the explicit optimal policies of Proposition 3 are derived.
--
--   **Formalization Note.** Two hypotheses are added to the page's "for any $v < \bar v$". First $v > 0$: at $v = 0$ promise keeping forces $\theta = 1$, every feasible policy with $\theta = 1$ is optimal, and these include policies with $(IC_b)$ binding. Second $\pi > 0$: the lemma concerns "the program (S) with $\pi = \hat\pi$" (proof, p. 39); at $\pi = 0$ the disclosure variables do not affect the objective, so the claim would fail.
-- source:
--   Fu & Trigilia, Voluntary Disclosure, Moral Hazard and Default Risk, working paper (August 28, 2019), p. 18, Lemma 1; proof p. 39

import Mathlib
import Definitions.Def_VolDisclosure_Evidence_Model

namespace VolDisclosure.Evidence

/-- Lemma 1 (p. 18; proof p. 39): for `0 < v < v̄`, every optimal policy of (S) has (ICg) and
(ICn) binding and (ICb) strict. -/
theorem lemma_1 (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 < π) (hπ1 : π < 1)
    (s : ℝ → ℝ) (hs : IsValue P π s) (v : ℝ) (hv0 : 0 < v) (hv1 : v < P.vBar)
    (a : Policy) (ha : IsOptimal P π v s a) :
    a.udh + a.wdh / (1 + P.r) = a.unh + a.wnh / (1 + P.r) ∧
    a.unh + a.wnh / (1 + P.r) = P.δ + a.unl + a.wnl / (1 + P.r) ∧
    a.udl + a.wdl / (1 + P.r) > a.unl + a.wnl / (1 + P.r) := by sorry

end VolDisclosure.Evidence
