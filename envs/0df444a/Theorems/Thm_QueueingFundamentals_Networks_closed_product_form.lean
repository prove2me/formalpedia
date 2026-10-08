-- Prove2me | Theorems.Thm_QueueingFundamentals_Networks_closed_product_form
-- name    : QueueingFundamentals.Networks.closed_product_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T09:10:59.138985+00:00
-- url     : https://prove2.me/theorems/4b46df8a-4554-46d9-9dab-05d4493e8836
-- title:
--   Eqs. (4.14)–(4.16) — the product-form steady state of a closed Jackson network
-- statement:
--   Consider a closed Jackson network of $k \ge 1$ nodes, each with a single exponential server of rate $\mu_i > 0$, with $N$ customers and an irreducible routing matrix $R = (r_{ij})$ whose rows sum to one. Let $\rho_1, \dots, \rho_k > 0$ be any positive solution of the traffic equations (4.16),
--   $$\mu_i\rho_i = \sum_{j=1}^{k} \mu_j r_{ji}\rho_j \qquad (i = 1, \dots, k).$$
--   Then a probability distribution $\{p_{\bar n}\}$ on the states $\{\bar n : n_1 + \cdots + n_k = N\}$ solves the flow-balance equations (4.14) if and only if
--   $$p_{n_1,\dots,n_k} = \frac{1}{G(N)}\,\rho_1^{n_1}\rho_2^{n_2}\cdots\rho_k^{n_k}, \qquad G(N) = \sum_{n_1+\cdots+n_k=N}\rho_1^{n_1}\cdots\rho_k^{n_k}.$$
--   In particular the steady-state solution exists and is unique.
--
--   This is the closed-network case of Jackson's theorem: although the node populations are dependent (they sum to $N$), the joint distribution has product form, and every performance measure of the network reduces to the constants $G(0), \dots, G(N)$.
--
--   **Formalization Note** The book states that (4.15) solves (4.14) (Problem 4.14) and that $C = G(N)^{-1}$ normalizes it; the book-wide convention that the steady-state distribution *is* the probability solution of the balance equations makes the uniqueness half explicit here, as an `↔`. Because (4.16) fixes $\rho$ only up to a positive scalar (p.196), the statement holds for every positive solution; $G(N)$ depends on the choice, the distribution does not.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.196, Eqs. (4.14), (4.15), (4.16) and the display of G(N); p.188 for the balance-equation convention

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson

namespace QueueingFundamentals.Networks

/-- Eqs. (4.14)–(4.16), pp.196: for a closed Jackson network of `k ≥ 1` single-server nodes with
service rates `μ_i > 0`, an irreducible routing matrix `R` and any positive solution `ρ` of the
traffic equations (4.16), a distribution `p` on the `N`-customer states is a steady-state solution
of the balance equations (4.14) if and only if it is the product form (4.15) normalized by
`G(N) = ∑_{n_1+⋯+n_k=N} ρ_1^{n_1} ⋯ ρ_k^{n_k}`. -/
theorem closed_product_form {k : ℕ} [NeZero k] (mu : Fin k → ℝ) (R : Fin k → Fin k → ℝ)
    (rho : Fin k → ℝ) (hmu : ∀ i, 0 < mu i) (hR : IsRoutingMatrix R) (hirr : IsIrreducible R)
    (hrho : ∀ i, 0 < rho i) (htraffic : IsTrafficSolution mu R rho) (N : ℕ)
    (p : (Fin k → ℕ) → ℝ) :
    IsClosedSteadyState mu R N p ↔ p = productForm (fun i n => rho i ^ n) N := by sorry

end QueueingFundamentals.Networks
