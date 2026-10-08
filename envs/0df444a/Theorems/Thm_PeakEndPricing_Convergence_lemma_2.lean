-- Prove2me | Theorems.Thm_PeakEndPricing_Convergence_lemma_2
-- name    : PeakEndPricing.Convergence.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:49:18.099604+00:00
-- url     : https://prove2.me/theorems/c84c3fd0-acbf-48b8-8522-6320e33f21bb
-- title:
--   Lemma 2 — the kinked short-term profit π = min(π_λ, π_γ) is supermodular in (p, r)
-- statement:
--   Let $d_0$ be any base demand, $\lambda \ge \gamma > 0$, and let $\pi(p,r) = p\,[d_0(p) - \lambda(p-r)^+ + \gamma(r-p)^+]$ be the short-term profit (5), with smooth components $\pi_k(p,r) = \pi_0(p) + k(r-p)p$, $k\in\{\lambda,\gamma\}$ (6). Then:
--
--   1. for every price $p \in \mathbf P = [0,\bar p]$ and every reference price $r$,
--   $$\pi(p,r) = \min\big(\pi_\lambda(p,r), \pi_\gamma(p,r)\big);$$
--   2. $\pi$ is supermodular on $\mathbf P \times \mathbf P$: for $p_l < p_h$ and $r_l < r_h$ in $\mathbf P$,
--   $$\pi(p_h,r_h) - \pi(p_l,r_h) \ge \pi(p_h,r_l) - \pi(p_l,r_l).$$
--
--   Supermodularity of the kinked profit is what makes optimal prices monotone in the reference price (Topkis' theorem) and is used throughout the analysis of steady states and price paths.
--
--   **Formalization Note** The profit $\pi$ is defined by (4)–(5), so the identity in part 1 is content (it uses $\lambda\ge\gamma$ and $p\ge0$). The paper states supermodularity "in $(p,r)$" without a domain; prices and reference prices lie in $\mathbf P$, which is the domain used here. The statement needs only $\lambda \ge \gamma > 0$ among the standing hypotheses; no assumption on $d_0$ is used.
-- source:
--   Nasiry and Popescu, Dynamic Pricing with Loss Averse Consumers and Peak-End Anchoring, INSEAD Working Paper 2009/20/DS/TOM, p. 10, Lemma 2 (with (4)–(6), p. 9)

import Mathlib
import Definitions.Def_PeakEndPricing_Convergence_Model

namespace PeakEndPricing.Convergence

theorem lemma_2 (pbar : ℝ) (d0 : ℝ → ℝ) (lam gam : ℝ) (hgam : 0 < gam) (hlam : gam ≤ lam) :
    (∀ p ∈ Set.Icc (0 : ℝ) pbar, ∀ r : ℝ,
      profit d0 lam gam p r = min (profitK d0 lam p r) (profitK d0 gam p r)) ∧
    SupermodularOn (profit d0 lam gam) (Set.Icc (0 : ℝ) pbar) (Set.Icc (0 : ℝ) pbar) := by sorry

end PeakEndPricing.Convergence
