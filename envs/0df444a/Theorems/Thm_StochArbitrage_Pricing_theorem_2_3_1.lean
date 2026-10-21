-- Prove2me | Theorems.Thm_StochArbitrage_Pricing_theorem_2_3_1
-- name    : StochArbitrage.Pricing.theorem_2_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:02.819788+00:00
-- url     : https://prove2.me/theorems/a024a6bd-3b6b-4773-84de-58c6e6477370
-- title:
--   Theorem 2.3.1 (corrected: finitely generated U), p. 11 (PDF 12) — no strict SAO iff E_F[m(x)x] ∈ ∆* for some m ∈ conv(M_(U,K))
-- statement:
--   Consider the single-period market of §2.1: $N$ base assets with payoff vector $x$ distributed according to $F$, a probability law supported in the box $[\mathrm{lo},\mathrm{hi}]^N$; a convex utility class $\mathcal U$ of continuously differentiable, strictly increasing, strictly concave functions, uniformly bounded on bounded sets; a closed bounded benchmark set $K$ whose portfolios satisfy the budget restriction $p^\mathsf T\kappa=c>0$; and the bounded overlay polytope $\Delta=\{\delta:A\delta\le a\}$ with $a\ge0$. Assume in addition that $\mathcal U$ is the convex hull of finitely many utility functions. Let
--   $$\Delta^\succ_{(\mathcal U,K,F)}=\{\delta\in\Delta: E_F[u(x^\mathsf T(\kappa+\delta))]-E_F[u(x^\mathsf T\kappa)]>0\ \text{for all }(u,\kappa)\in\mathcal U\times K\}$$
--   be the set of strict stochastic arbitrage opportunities, $\mathcal M_{(\mathcal U,K)}=\{x\mapsto d\,u'(x^\mathsf T\kappa): (u,\kappa)\in\mathcal U\times K,\ d>0\}$ the marginal-utility stochastic discount factors, and $\Delta^*=\{A^\mathsf T\sigma:\sigma\ge0,\ a^\mathsf T\sigma\le0\}$ the polar cone of the overlay set. Then
--   $$\Delta^\succ_{(\mathcal U,K,F)}=\varnothing\quad\Longleftrightarrow\quad E_F[m(x)x]\in\Delta^*\ \text{for some } m\in\operatorname{conv}(\mathcal M_{(\mathcal U,K)}).$$
--
--   In words: no overlay improves every admissible benchmark for every admissible investor exactly when some mixture of marginal-utility discount factors assigns the base assets present values that are compatible with the shadow prices of the overlay constraints. This is the paper's Existential Condition, the asset-pricing characterization of the absence of stochastic arbitrage.
--
--   **Formalization Note.** The printed Theorem 2.3.1 assumes only that $\mathcal U$ is convex and uniformly bounded. Its "only if" direction is then false: with a riskless asset $x_1\equiv1$, a second asset $x_2\in\{2,-1\}$ with probability $\tfrac12$ each, the benchmark $K=\{(1,0)\}$ and overlays $\Delta=\{(0,t):t\in[0,1]\}$, the convex hull of the utilities $u_n(y)=-\log(1+e^{n(1-y)})/n$ admits no strict SAO, while every discount factor at the riskless benchmark is a positive constant and prices $x_2$ positively, outside $\Delta^*=\{q:q_2\le0\}$. The hypothesis that $\mathcal U$ is finitely generated is the paper's own computational setting ($\mathcal U^{(0)}$ with $\mathrm{cl}(\mathcal U)=\mathrm{conv}(\mathcal U^{(0)})$, p. 14, and system (6), p. 15). $K$ remains an arbitrary closed bounded set, neither finite nor convex. The "if" direction holds without the extra hypothesis and is a separate milestone. The paper's $a$ of $\mathcal X=[a,b]$ is `lo`, and the right-hand side of $A\delta\le a$ is `aVec`.
-- source:
--   Arvanitis & Post, Ordering Arbitrage Portfolios and Finding Arbitrage Opportunities, AUEB Department of Economics Working Paper 04-2022 (March 2022; published as Generalized Stochastic Arbitrage Opportunities, Management Science 2024), p. 11 (PDF 12), Theorem 2.3.1; proof pp. 34–35 (PDF 35–36); finitely generated U: p. 14 (PDF 15) and system (6), p. 15 (PDF 16)

import Mathlib
import Definitions.Def_StochArbitrage_Pricing_Model

namespace StochArbitrage.Pricing

/-- Theorem 2.3.1, corrected by requiring a finitely generated utility class. -/
theorem theorem_2_3_1 {N R : ℕ} (M : Market N R) (U : Set (ℝ → ℝ))
    (K : Set (Fin N → ℝ)) (hS : M.Standing U K)
    (hU : ∃ U₀ : Set (ℝ → ℝ), U₀.Finite ∧ U = convexHull ℝ U₀) :
    M.strictSAOSet U K = ∅ ↔
      ∃ m ∈ convexHull ℝ (sdfSet U K), M.presentValue m ∈ M.polarCone := by sorry

end StochArbitrage.Pricing
