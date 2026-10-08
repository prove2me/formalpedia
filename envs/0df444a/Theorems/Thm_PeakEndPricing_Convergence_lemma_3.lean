-- Prove2me | Theorems.Thm_PeakEndPricing_Convergence_lemma_3
-- name    : PeakEndPricing.Convergence.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:49:19.698597+00:00
-- url     : https://prove2.me/theorems/5d6a7494-2084-4d2b-9798-86344e775f83
-- title:
--   Lemma 3 — for m ≤ p, J(m, p) ≤ J^ν_m(p): the smooth problems (8) bound the value function
-- statement:
--   Under the standing hypotheses of Section 3, let $J(m,p)$ be the value function of the peak-end pricing problem (7), and for $\nu\in[0,1]$ and $m\in\mathbf P$ let $J^\nu_m(p)$ be the value function of the smooth Problem (8): the supremum, over price sequences in $\mathbf P$ started from last price $p_0 = p$, of
--   $$\sum_{t\ge1}\beta^{t-1}\Big[(1-\nu)\pi_\lambda\big(p_t,\theta m + (1-\theta)p_{t-1}\big) + \nu\,\pi_\gamma(p_t,p_{t-1})\Big].$$
--   Then for every $\nu \in [0,1]$ and all $m, p\in\mathbf P$ with $m\le p$,
--   $$J(m,p) \le J^\nu_m(p).$$
--
--   The family $J^\nu_m$ of smooth problems with one-dimensional state provides upper bounds for the non-smooth two-dimensional problem; matching steady states of the bounds with those of Problem (7) is the paper's route to Proposition 1.
-- source:
--   Nasiry and Popescu, Dynamic Pricing with Loss Averse Consumers and Peak-End Anchoring, INSEAD Working Paper 2009/20/DS/TOM, p. 10, Lemma 3

import Mathlib
import Definitions.Def_PeakEndPricing_Convergence_Model

namespace PeakEndPricing.Convergence

theorem lemma_3 (pbar : ℝ) (d0 : ℝ → ℝ) (lam gam theta beta : ℝ)
    (hst : Standing pbar d0 lam gam theta beta)
    (nu : ℝ) (hnu : nu ∈ Set.Icc (0 : ℝ) 1) (m p : ℝ)
    (hm : m ∈ Set.Icc (0 : ℝ) pbar) (hp : p ∈ Set.Icc (0 : ℝ) pbar) (hmp : m ≤ p) :
    J pbar d0 lam gam theta beta m p ≤ auxValue pbar d0 lam gam theta beta m nu p := by sorry

end PeakEndPricing.Convergence
