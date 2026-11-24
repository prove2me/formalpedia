-- Prove2me | Theorems.Thm_WhenToTrustYourModel_markov_tv_bound
-- name    : WhenToTrustYourModel.markov_tv_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T11:17:29.935589+00:00
-- url     : https://prove2.me/theorems/eac5022c-c254-4d21-a7f3-b5e5237ffdcf
-- title:
--   Lemma B.2 (as proved): Markov chain TVD bound, time-varying
-- statement:
--   Let $\mathcal S$ be a finite set, let $p_{1,t}(s'\mid s)$ and $p_{2,t}(s'\mid s)$ ($t=0,1,2,\dots$) be two sequences of Markov transition kernels on $\mathcal S$ (the kernels may change with time), and run both chains from the same initial distribution $p_1^0=p_2^0=\mu_0$, chain $i$ moving from time $t$ to $t+1$ with $p_{i,t}$; write $p_i^t$ for the state marginal at time $t$. Suppose that for some $\delta$
--
--   $$\max_t E_{s\sim p_1^t}\big[D_{TV}\big(p_{1,t}(\cdot\mid s)\|p_{2,t}(\cdot\mid s)\big)\big]\le\delta .$$
--
--   Then for every $t\ge0$
--
--   $$D_{TV}\big(p_1^t\|p_2^t\big)\le t\,\delta .$$
--
--   The state marginals of two chains drift apart at most linearly in time, at the rate of the expected one-step discrepancy.
--
--   **Formalization Note** The paper's statement assumes a bound on the expected KL divergence $E_{s\sim p_1^t}D_{KL}(p_1(\cdot\mid s)\|p_2(\cdot\mid s))\le\delta$, but its proof defines $\delta_t$ as the expected total variation and bounds that. With the KL hypothesis the statement is false (a chain with $D_{TV}=0.1$ and $D_{KL}\approx0.0204$ at the first step). The Lean statement uses the total variation hypothesis, as proved. The kernels are allowed to depend on time, as in the lemma's title ("time-varying") and its use in the proof of Lemma B.4.
-- source:
--   Janner, Fu, Zhang and Levine, When to Trust Your Model: Model-Based Policy Optimization, arXiv:1906.08253v3 (NeurIPS 2019), Appendix B, Lemma B.2, p. 15

import Mathlib
import Definitions.Def_WhenToTrustYourModel_Basic

open Finset

namespace WhenToTrustYourModel

theorem markov_tv_bound {S : Type*} [Fintype S]
    (μ₀ : S → ℝ) (hμ₀ : IsDist μ₀)
    (K₁ K₂ : ℕ → S → S → ℝ) (hK₁ : ∀ t s, IsDist (K₁ t s)) (hK₂ : ∀ t s, IsDist (K₂ t s))
    (δ : ℝ) (hδ : ∀ t, ∑ s, chainDist μ₀ K₁ t s * tvDist (K₁ t s) (K₂ t s) ≤ δ)
    (t : ℕ) :
    tvDist (chainDist μ₀ K₁ t) (chainDist μ₀ K₂ t) ≤ t * δ := by sorry

end WhenToTrustYourModel
