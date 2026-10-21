-- Prove2me | Theorems.Thm_StochArbitrage_Pricing_convexification
-- name    : StochArbitrage.Pricing.convexification
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:07.102995+00:00
-- url     : https://prove2.me/theorems/fb0f9e06-2ae6-4de2-bb99-90b9094810e4
-- title:
--   Proof of Theorem 2.3.1, (9)–(10), p. 35 (PDF 36) — convexification of M_(U,K), pointwise form
-- statement:
--   Assume the standing assumptions of §2.1 for the payoff law $F$, the utility class $\mathcal U$, the benchmark set $K$ and the overlay polytope $\Delta$, and let $\mathcal M_{(\mathcal U,K)}$ be the set of scaled marginal-utility discount factors $x\mapsto d\,u'(x^\mathsf T\kappa)$, $d>0$. For every overlay $\delta\in\Delta$,
--   $$\bigl(\exists\, m\in\operatorname{conv}(\mathcal M_{(\mathcal U,K)}):\ E_F[m(x)x]^\mathsf T\delta\le0\bigr)\iff\bigl(\exists\, m\in\mathcal M_{(\mathcal U,K)}:\ E_F[m(x)x]^\mathsf T\delta\le0\bigr).$$
--
--   The objective $(\delta,m)\mapsto E_F[m(x)x^\mathsf T\delta]$ is bilinear, so passing from the discount factors to their convex hull does not change whether the inner problem over discount factors can reach a nonpositive value. This is the step from (9) to (10) in the proof of Theorem 2.3.1.
--
--   **Formalization Note.** The printed (9) and (10) are written as $\sup_\Delta\inf_{\mathcal M}E_F[m(x)x^\mathsf T\delta]\le0$. Because each element of $\mathcal M_{(\mathcal U,K)}$ carries a free scale $d>0$, those infima are never positive, so the displays taken literally hold trivially. The item poses the sign content that the proof uses, for each fixed $\delta$. $\operatorname{conv}$ is the convex hull in the vector space of real functions on $\mathbb R^N$, i.e. finite convex combinations.
-- source:
--   Arvanitis & Post, Ordering Arbitrage Portfolios and Finding Arbitrage Opportunities, AUEB Department of Economics Working Paper 04-2022 (March 2022; published as Generalized Stochastic Arbitrage Opportunities, Management Science 2024), proof of Theorem 2.3.1, (9)–(10), p. 35 (PDF 36)

import Mathlib
import Definitions.Def_StochArbitrage_Pricing_Model

namespace StochArbitrage.Pricing

/-- The pointwise content of the convexification step (9)–(10). -/
theorem convexification {N R : ℕ} (M : Market N R) (U : Set (ℝ → ℝ))
    (K : Set (Fin N → ℝ)) (hS : M.Standing U K)
    (δ : Fin N → ℝ) (hδ : δ ∈ M.overlaySet) :
    (∃ m ∈ convexHull ℝ (sdfSet U K), M.presentValue m ⬝ᵥ δ ≤ 0) ↔
      (∃ m ∈ sdfSet U K, M.presentValue m ⬝ᵥ δ ≤ 0) := by sorry

end StochArbitrage.Pricing
