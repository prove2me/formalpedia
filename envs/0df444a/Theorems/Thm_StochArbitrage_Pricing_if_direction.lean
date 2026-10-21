-- Prove2me | Theorems.Thm_StochArbitrage_Pricing_if_direction
-- name    : StochArbitrage.Pricing.if_direction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:04.090383+00:00
-- url     : https://prove2.me/theorems/c7cca64a-0c8b-4de8-b479-f3f7015924f9
-- title:
--   Theorem 2.3.1, 'if' direction, p. 11 (PDF 12) — a mixture of IMRS SDFs pricing the assets inside ∆* rules out strict SAOs
-- statement:
--   Assume the standing assumptions of §2.1: the payoff law $F$ is a probability measure supported in $[\mathrm{lo},\mathrm{hi}]^N$; $\mathcal U$ is a convex class of continuously differentiable, strictly increasing, strictly concave utilities, uniformly bounded on bounded sets; $K$ is closed, bounded and satisfies the budget restriction $p^\mathsf T\kappa=c>0$; and $\Delta=\{\delta:A\delta\le a\}$ is bounded with $a\ge0$. If some convex combination $m$ of the marginal-utility discount factors $x\mapsto d\,u'(x^\mathsf T\kappa)$ ($d>0$, $(u,\kappa)\in\mathcal U\times K$) prices the base assets inside the polar cone, then there is no strict stochastic arbitrage opportunity:
--   $$\bigl(\exists\, m\in\operatorname{conv}(\mathcal M_{(\mathcal U,K)}):\ E_F[m(x)x]\in\Delta^*\bigr)\ \Longrightarrow\ \Delta^\succ_{(\mathcal U,K,F)}=\varnothing .$$
--
--   This is the "if" half of Theorem 2.3.1, in the paper's full generality: no finiteness of $\mathcal U$ or $K$ is assumed. It is the direction that turns a pricing system into a certificate that no overlay improves every benchmark for every admissible investor.
--
--   **Formalization Note.** $\Delta^*$ is the set $\{A^\mathsf T\sigma:\sigma\ge0,\ a^\mathsf T\sigma\le0\}$ printed on p. 11, not the abstract polar $\{q: q^\mathsf T\delta\le0\ \forall\delta\in\Delta\}$. The converse half needs an extra hypothesis; see the goal theorem.
-- source:
--   Arvanitis & Post, Ordering Arbitrage Portfolios and Finding Arbitrage Opportunities, AUEB Department of Economics Working Paper 04-2022 (March 2022; published as Generalized Stochastic Arbitrage Opportunities, Management Science 2024), p. 11 (PDF 12), Theorem 2.3.1, 'if' direction; proof pp. 34–35 (PDF 35–36)

import Mathlib
import Definitions.Def_StochArbitrage_Pricing_Model

namespace StochArbitrage.Pricing

/-- The unrestricted implication from the pricing condition to no strict SAO. -/
theorem if_direction {N R : ℕ} (M : Market N R) (U : Set (ℝ → ℝ))
    (K : Set (Fin N → ℝ)) (hS : M.Standing U K) :
    (∃ m ∈ convexHull ℝ (sdfSet U K), M.presentValue m ∈ M.polarCone) →
      M.strictSAOSet U K = ∅ := by sorry

end StochArbitrage.Pricing
