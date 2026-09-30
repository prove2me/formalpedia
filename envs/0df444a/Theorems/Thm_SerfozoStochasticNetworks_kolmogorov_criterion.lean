-- Prove2me | Theorems.Thm_SerfozoStochasticNetworks_kolmogorov_criterion
-- name    : SerfozoStochasticNetworks.kolmogorov_criterion
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-19T02:52:29.252983+00:00
-- url     : https://prove2.me/theorems/7ecfd3c6-97b5-4ab0-b8df-9f1c4718dc42
-- title:
--   Theorem 2.8 — Kolmogorov's criterion and the canonical invariant measure
-- statement:
--   Let $q$ be a non-negative rate function on a state space with the two-way communication property
--   — $q(x,y)>0$ exactly when $q(y,x)>0$ — and suppose $q$ is irreducible, every state being
--   reachable from every other along a path of positive rates. Write $\rho(x,y)=q(x,y)/q(y,x)$.
--
--   Then all of the following hold.
--
--   1. **$q$ is reversible if and only if Kolmogorov's criterion holds:** for every $n$ and every
--      sequence $x_0,\dots,x_n$ with $x_n=x_0$,
--      $$\prod_{i=1}^{n}q(x_{i-1},x_i)=\prod_{i=1}^{n}q(x_i,x_{i-1}).$$
--   2. **$q$ is reversible if and only if the rate ratios are path-independent:** for any two paths
--      with the same initial state and the same final state, the products
--      $\prod_i\rho(x_{i-1},x_i)$ along them agree.
--   3. **If $q$ is reversible then, for every choice of origin $x^0$, there is a strictly positive
--      $\pi$ with $\pi(x^0)=1$ satisfying the detailed balance equations and given by
--      $$\pi(x)=\prod_{i=1}^{n}\rho(x_{i-1},x_i)$$
--      for every path $x^0=x_0,\dots,x_n=x$ from the origin to $x$.**
--
--   The criterion is a condition on the rates alone, with no reference to an unknown measure, and
--   the third part turns it into a construction: the invariant measure is read off as a product of
--   rate ratios along any path.
--
--   **Formalization Note** Kolmogorov's criterion is asserted for **arbitrary** closed sequences,
--   not merely for closed paths, exactly as the book states it. Under two-way communication the two
--   readings coincide: if some rate along the sequence vanishes, so does its reverse, and both
--   products are zero.
--
--   In the third part the measure is produced rather than defined: the conclusion asserts the
--   existence of a $\pi$ that agrees with the ratio product along **every** path from the origin,
--   which is the content of expression (2.9) without having to choose a path for each state. A path
--   of length zero gives the empty product $1$, consistent with $\pi(x^0)=1$.
--
--   Irreducibility is used for the third part, to reach every state from the origin, and for the
--   implication from the criterion to reversibility. Reversibility here means the existence of some
--   positive measure satisfying detailed balance; no normalization is claimed, and whether $\pi$
--   can be normalized to a probability distribution is not part of the statement.
--
--   The state space is an arbitrary type and $q$ an arbitrary non-negative function, so the
--   statement applies verbatim to a discrete-time chain with $q$ read as transition probabilities,
--   as the book points out.
-- source:
--   Serfozo, Introduction to Stochastic Networks, Springer 1999, p. 50 (PDF p. 63), Theorem 2.8: "The following statements are equivalent. (i) The transition function q is reversible. (ii) (Kolmogorov Criterion) For each n and x0, x1, ..., xn in E with xn = x0, prod_{i=1}^n q(x_{i-1}, x_i) = prod_{i=1}^n q(x_i, x_{i-1}). (iii) For each path x0, x1, ..., xn in E, the product prod_{i=1}^n rho(x_{i-1}, x_i) depends on x0, ..., xn and n only through x0, xn. If q is reversible, then an invariant measure for it is pi(x) = prod_{i=1}^n rho(x_{i-1}, x_i), x in E\{x0}, (2.9) and pi(x0) = 1, where x0, x1, ..., xn = x is any path and x0 is an arbitrary state viewed as an origin." sha256 919f20ee082ec19faa80bdd923a5529fce9c4b6d3264fdb77c5efa64256bb463

import Mathlib
import Definitions.Def_SerfozoStochasticNetworks_Reversible

namespace SerfozoStochasticNetworks

theorem kolmogorov_criterion {E : Type*} (q : E → E → ℝ)
    (hq : ∀ x y, 0 ≤ q x y) (htw : TwoWay q) (hirr : IsIrreducible q) :
    (IsReversible q ↔ KolmogorovCriterion q) ∧ (IsReversible q ↔ RatioInvariance q) ∧
    (IsReversible q → ∀ x₀ : E, ∃ π : E → ℝ, (∀ x, 0 < π x) ∧ π x₀ = 1 ∧ DetailedBalance q π ∧
      ∀ (n : ℕ) (p : Fin (n + 1) → E), IsPath q p → p 0 = x₀ →
        π (p (Fin.last n)) = pathRatio q p) := by sorry

end SerfozoStochasticNetworks
