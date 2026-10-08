-- Prove2me | Theorems.Thm_PeakEndPricing_Convergence_lemma_1
-- name    : PeakEndPricing.Convergence.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:49:14.397757+00:00
-- url     : https://prove2.me/theorems/d040b594-404a-4513-84f4-60a8a31c4c85
-- title:
--   Lemma 1 — the value function J(m, p) is increasing in both arguments
-- statement:
--   Consider the peak-end pricing model under the standing hypotheses of Section 3 (Assumption 1 on the base demand $d_0$, $\lambda \ge \gamma > 0$, $\theta\in(0,1]$, $\beta\in(0,1)$, $\pi_0$ differentiable on $\mathbf P = [0,\bar p]$). Let $J(m,p)$ be the value function: the supremum, over price sequences in $\mathbf P$, of the discounted profit $\sum_{t\ge1}\beta^{t-1}\pi(p_t,r_t)$ started from minimum price $m$ and last price $p$.
--
--   Then $J$ is (weakly) increasing in each argument: for $m, m', p, p' \in \mathbf P$,
--   $$m \le m' \implies J(m,p) \le J(m',p), \qquad p \le p' \implies J(m,p) \le J(m,p').$$
--
--   A memory of higher prices (a higher minimum price or a higher last price) raises consumers' reference price and lets the firm extract more profit. The result is used to compare value functions in the proofs of Lemma 3 and of Proposition 2.
--
--   **Formalization Note** The paper states the monotonicity without restricting to $m \le p$; the Lean statement likewise covers all $m, m', p, p' \in \mathbf P$.
-- source:
--   Nasiry and Popescu, Dynamic Pricing with Loss Averse Consumers and Peak-End Anchoring, INSEAD Working Paper 2009/20/DS/TOM, p. 8, Lemma 1

import Mathlib
import Definitions.Def_PeakEndPricing_Convergence_Model

namespace PeakEndPricing.Convergence

theorem lemma_1 (pbar : ℝ) (d0 : ℝ → ℝ) (lam gam theta beta : ℝ)
    (hst : Standing pbar d0 lam gam theta beta) :
    (∀ m m' p : ℝ, m ∈ Set.Icc (0 : ℝ) pbar → m' ∈ Set.Icc (0 : ℝ) pbar →
      p ∈ Set.Icc (0 : ℝ) pbar → m ≤ m' →
        J pbar d0 lam gam theta beta m p ≤ J pbar d0 lam gam theta beta m' p) ∧
    (∀ m p p' : ℝ, m ∈ Set.Icc (0 : ℝ) pbar → p ∈ Set.Icc (0 : ℝ) pbar →
      p' ∈ Set.Icc (0 : ℝ) pbar → p ≤ p' →
        J pbar d0 lam gam theta beta m p ≤ J pbar d0 lam gam theta beta m p') := by sorry

end PeakEndPricing.Convergence
