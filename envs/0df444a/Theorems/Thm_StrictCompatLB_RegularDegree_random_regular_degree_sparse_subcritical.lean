-- Prove2me | Theorems.Thm_StrictCompatLB_RegularDegree_random_regular_degree_sparse_subcritical
-- name    : StrictCompatLB.RegularDegree.random_regular_degree_sparse_subcritical
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:08:02.80952+00:00
-- url     : https://prove2.me/theorems/ed72b892-46fc-46d2-9c76-3050cf96eb8c
-- title:
--   Theorem 3.5 — random graphs with server degree c(N) are a.s. proportionally sparse and subcritical
-- statement:
--   Let $c(N)\le M(N)$ be a sequence of positive integers satisfying
--   $$c(N)\to\infty\qquad\text{and}\qquad\frac{Nc(N)}{M(N)\ln N}\to\infty\qquad(N\to\infty).$$
--   For each $N$, construct the bipartite compatibility graph $G_N$ between $N$ servers $V_N$ and $M(N)$ dispatchers $W_N$ as follows: each server $v\in V_N$ selects $c(N)$ dispatchers uniformly at random without replacement, independently over servers. The graphs for different $N$ live on one probability space with arbitrary joint law. Let $d\ge2$ be the JSQ($d$) sample size. Then, almost surely, the sequence $\{G_N\}_{N\ge1}$
--
--   1. is **proportionally sparse**: for every $\varepsilon>0$,
--   $$\sup_{U\subseteq V_N}\Big|\Big\{w\in W_N:\Big|\frac{|\mathcal N_w\cap U|}{|\mathcal N_w|}-\frac{|U|}{N}\Big|\ge\varepsilon\Big\}\Big|\Big/M(N)\to0;$$
--   2. satisfies the **subcriticality condition**: there are probability distributions $\gamma^U_w$ on the sets $U$ with
--   $$\limsup_{N\to\infty}\max_{v\in V_N}\frac{N}{M(N)}\sum_{w\in W_N}\binom{|\mathcal N_w|}{k_w}^{-1}\sum_{\substack{U\subseteq\mathcal N_w\\|U|=k_w}}\gamma^U_w(v)\le1,\qquad k_w=\min(d,|\mathcal N_w|).$$
--
--   Combined with Theorem 3.4 of the paper, this means that JSQ($d$) on such a random compatibility graph, in which each server is compatible with only $c(N)$ task types, has the same mean-field limit and steady state as the fully flexible system.
--
--   **Formalization Note** The theorem's last sentence, "Consequently, the conclusions of Theorem 3.4 hold", is not formalized: it composes this result with the main theorem of mission 1 of this series. The construction's printed edge pool "$\{(v,w)\in V_N\times W_N\mid v\in V_N\}$" is read as $\{(v,w):w\in W_N\}$ for the fixed server $v$ (degree exactly $c(N)$ per server, as §3.2 says). Only the law of each $G_N$ is prescribed (p. 13); independence across $N$ is not assumed. Proportional sparsity is the limit condition (3.1) without connectivity, since these random graphs are disconnected for small $N$. Subcriticality uses weights constrained on nonempty $U$ and the normaliser $\binom{|\mathcal N_w|}{k_w}$ in place of the paper's $\binom{|\mathcal N_w|}{d}$, which is $1/0$ when $|\mathcal N_w|<d$. The growth conditions are real limits. Lean's $\ln 1=0$ affects only finitely many terms.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 13, Theorem 3.5

import Mathlib
import Definitions.Def_StrictCompatLB_RegularDegree_GraphConditions
import Definitions.Def_StrictCompatLB_RegularDegree_RandomServerRegular

open Finset Filter MeasureTheory Topology

namespace StrictCompatLB.RegularDegree

theorem random_regular_degree_sparse_subcritical
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M c : ℕ → ℕ) (hc_pos : ∀ N, 1 ≤ c N) (hcM : ∀ N, c N ≤ M N)
    (adj : (N : ℕ) → Ω → Fin N → Fin (M N) → Bool) (hadj : IsRandomServerRegular P M c adj)
    (d : ℕ) (hd : 2 ≤ d)
    (hc : Tendsto (fun N : ℕ => (c N : ℝ)) atTop atTop)
    (hcM_log : Tendsto (fun N : ℕ => (N : ℝ) * (c N : ℝ) / ((M N : ℝ) * Real.log (N : ℝ)))
      atTop atTop) :
    ∀ᵐ ω ∂P, StrictCompatLB.MeanField.IsPropSparse M (randomGraph M adj ω) ∧
      StrictCompatLB.MeanField.IsSubcritical d M (randomGraph M adj ω) := by sorry

end StrictCompatLB.RegularDegree
