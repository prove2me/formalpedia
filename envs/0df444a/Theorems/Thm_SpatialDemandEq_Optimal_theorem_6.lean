-- Prove2me | Theorems.Thm_SpatialDemandEq_Optimal_theorem_6
-- name    : SpatialDemandEq.Optimal.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:28.658979+00:00
-- url     : https://prove2.me/theorems/d2e48351-0d0f-419b-8747-441fba4de951
-- title:
--   Theorem 6, p. 19 — under locally optimal service rates μ**, the decentralized equilibrium partition equals the locally optimal partition 𝒜**
-- statement:
--   Assume the standing assumptions of the spatial model: $\mathcal S \subseteq \mathbb R^n$ closed and convex; the normalized demand $\nu$ a probability measure on $\mathcal S$, absolutely continuous with respect to Lebesgue measure; $d$ a continuous metric on $\mathbb R^n$ and facilities $x_1,\dots,x_K \in \mathcal S$ ($K \ge 1$), with the distances $d_k(x) = d(x,x_k)$ $\nu$-integrable and regular (the law of $d_j - d_k$ under $\nu$ has a density for $j \ne k$); $c > 0$, $\lambda > 0$; and a budget $B > \lambda$.
--
--   Let $(\mu^{**}, \mathcal A^{**})$ be a local optimum of the social-cost problem (15),
--   $$\min_{\mathcal A, \mu}\ \sum_k A_k\frac{c}{\mu_k - \lambda A_k} + \sum_k\int_{\mathcal A_k} d_k\,d\nu \quad \text{s.t. (10)–(12)},\ \sum_k \mu_k = B,$$
--   with every area $A^{**}_k = \nu(\mathcal A^{**}_k)$ positive. Then:
--
--   1. a decentralized demand equilibrium under the service rates $\mu^{**}$ exists, i.e. a partition $\mathcal A^*$ of $\mathcal S$ with $\lambda A^*_k < \mu^{**}_k$ and
--   $$d_k(x) + \frac{c}{\mu^{**}_k - \lambda A^*_k} \le d_j(x) + \frac{c}{\mu^{**}_j - \lambda A^*_j} \qquad \text{for all } x \in \mathcal A^*_k,\ j \ne k; \tag{1}$$
--   2. every such equilibrium coincides with the optimum: $\mathcal A^* = \mathcal A^{**}$ up to $\nu$-null sets, i.e. $\nu(\mathcal A^*_k \,\triangle\, \mathcal A^{**}_k) = 0$ for every $k$.
--
--   So when the service rates are set to their (locally) socially optimal values, selfish customers who trade travel distance against expected M/M/1 waiting time partition the region exactly as a central planner would; in particular the globally optimal social welfare is attainable by decentralized behaviour.
--
--   **Formalization Note** The page's "the equilibrium partition attained in the decentralized model under $\mu^{**}$" presupposes existence and uniqueness; both are part of the conclusion. "$\mathcal A^* = \mathcal A^{**}$" is equality up to $\nu$-null sets, since a local optimum stays one after a null modification. The hypothesis that every area of $\mathcal A^{**}$ is positive is added (at a zero area, (17) gives a zero rate and the weight (16) is undefined). Each $d_k$ is assumed $\nu$-integrable (otherwise (15) is not a real number), the positive intensity $\lambda(x) > 0$ is dropped, and the capacity condition $\sum_k \mu^{**}_k > \lambda$ of §3 follows from $\sum_k \mu^{**}_k = B > \lambda$. Waiting costs are real-valued with explicit stability conjuncts $\lambda A_k < \mu_k$, and the local-optimum neighbourhood is $|\mu'_k - \mu^{**}_k| < \varepsilon$, $\nu(\mathcal A'_k \triangle \mathcal A^{**}_k) < \varepsilon$ for all $k$.
-- source:
--   Carlsson, Peng & Ryzhov, Demand Equilibria in Spatial Service Systems, SSRN preprint 4794156 (version of 2024-04-14), p. 19, Theorem 6; social cost (15), p. 17; equilibrium (1), p. 7

import Mathlib
import Definitions.Def_SpatialDemandEq_Optimal_Model

open MeasureTheory

namespace SpatialDemandEq.Optimal

theorem theorem_6 {n K : ℕ} (S : Set (E n)) (ν : Measure (E n)) (dst : E n → E n → ℝ)
    (xs : Fin K → E n) (c lam B : ℝ) (hS : Standing S ν dst xs c lam) (hB : lam < B)
    (μ : Fin K → ℝ) (A : Fin K → Set (E n))
    (hopt : IsLocalOpt ν S (distFn dst xs) c lam B μ A)
    (hpos : ∀ k, 0 < area ν (A k)) :
    (∃ A' : Fin K → Set (E n), IsDecentralizedEq ν S (distFn dst xs) c lam μ A') ∧
      ∀ A' : Fin K → Set (E n), IsDecentralizedEq ν S (distFn dst xs) c lam μ A' →
        ∀ k, ν (symmDiff (A' k) (A k)) = 0 := by sorry

end SpatialDemandEq.Optimal
