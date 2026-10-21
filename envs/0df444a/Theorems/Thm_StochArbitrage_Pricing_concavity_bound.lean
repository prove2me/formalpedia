-- Prove2me | Theorems.Thm_StochArbitrage_Pricing_concavity_bound
-- name    : StochArbitrage.Pricing.concavity_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:21.020983+00:00
-- url     : https://prove2.me/theorems/aa02792c-4662-45aa-869b-515a27cb0876
-- title:
--   Proof of Theorem 2.3.1, p. 34 (PDF 35) — concavity bound D(u,κ,δ,F) ≤ E_F[u′(xᵀκ)x]ᵀδ
-- statement:
--   Assume the standing assumptions of §2.1 for the payoff law $F$, the utility class $\mathcal U$, the benchmark set $K$ and the overlay polytope $\Delta$. For every $u\in\mathcal U$, $\kappa\in K$ and $\delta\in\Delta$, the expected utility increment is bounded above by its first-order approximation at the benchmark:
--   $$D(u,\kappa,\delta,F)=E_F[u(x^\mathsf T(\kappa+\delta))]-E_F[u(x^\mathsf T\kappa)]\ \le\ E_F[u'(x^\mathsf T\kappa)\,x]^\mathsf T\delta .$$
--
--   In particular, if the marginal-utility value $E_F[u'(x^\mathsf T\kappa)x]^\mathsf T\delta$ is nonpositive for some $(u,\kappa)\in\mathcal U\times K$, then $\delta$ does not strictly enhance $\kappa$ for $u$, so $\delta\notin\Delta^\succ_{(\mathcal U,K,F)}$. This is the use the proof of Theorem 2.3.1 makes of the concavity of the utility function.
--
--   **Formalization Note.** The cited sentence states that, by concavity, $D(u,\kappa,\delta,F)\le0$ is equivalent to $\lambda=\kappa$ being the optimum on the segment $\{\kappa+\theta\delta:\theta\in[0,1]\}$. That equivalence fails in the direction $D\le0\Rightarrow$ optimality (see the KKT item). This item poses the valid consequence of concavity that the "if" direction of Theorem 2.3.1 needs, not the printed equivalence.
-- source:
--   Arvanitis & Post, Ordering Arbitrage Portfolios and Finding Arbitrage Opportunities, AUEB Department of Economics Working Paper 04-2022 (March 2022; published as Generalized Stochastic Arbitrage Opportunities, Management Science 2024), proof of Theorem 2.3.1, p. 34 (PDF 35), 'Due to concavity of the utility function …'

import Mathlib
import Definitions.Def_StochArbitrage_Pricing_Model

namespace StochArbitrage.Pricing

open MeasureTheory

/-- The concavity inequality used in the proof of Theorem 2.3.1. -/
theorem concavity_bound {N R : ℕ} (M : Market N R) (U : Set (ℝ → ℝ))
    (K : Set (Fin N → ℝ)) (hS : M.Standing U K)
    (u : ℝ → ℝ) (hu : u ∈ U) (κ δ : Fin N → ℝ)
    (hκ : κ ∈ K) (hδ : δ ∈ M.overlaySet) :
    M.D u κ δ ≤ M.presentValue (fun x => deriv u (x ⬝ᵥ κ)) ⬝ᵥ δ := by sorry

end StochArbitrage.Pricing
