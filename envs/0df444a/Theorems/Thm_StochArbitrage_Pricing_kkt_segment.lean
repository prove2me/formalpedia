-- Prove2me | Theorems.Thm_StochArbitrage_Pricing_kkt_segment
-- name    : StochArbitrage.Pricing.kkt_segment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:00.327989+00:00
-- url     : https://prove2.me/theorems/4113d816-9c89-4e04-a3bb-24ce2aa2a94e
-- title:
--   Proof of Theorem 2.3.1, p. 34 (PDF 35) — KKT condition on the segment κ + θδ (the true part of the step)
-- statement:
--   Assume the standing assumptions of §2.1 for the payoff law $F$, the utility class $\mathcal U$, the benchmark set $K$ and the overlay polytope $\Delta$. Fix $u\in\mathcal U$, $\kappa\in K$ and $\delta\in\Delta$, and consider the expected utility along the segment from the benchmark to the enhanced portfolio,
--   $$\varphi(\theta)=E_F[u(x^\mathsf T(\kappa+\theta\delta))],\qquad \theta\in[0,1].$$
--   Then $\theta=0$ (that is, $\lambda=\kappa$) maximizes $\varphi$ on $[0,1]$ if and only if the marginal-utility value of the overlay is nonpositive:
--   $$\varphi(0)=\max_{\theta\in[0,1]}\varphi(\theta)\quad\Longleftrightarrow\quad E_F[u'(x^\mathsf T\kappa)\,x]^\mathsf T\delta\le 0.$$
--
--   This is the Karush–Kuhn–Tucker condition invoked in the proof of Theorem 2.3.1 for the problem $\sup_{\lambda\in\Theta}E_F[u(x^\mathsf T\lambda)]$ over $\Theta=\{\kappa+\theta\delta:\theta\in[0,1]\}$.
--
--   **Formalization Note.** The proof on p. 34 first asserts that $D(u,\kappa,\delta,F)\le 0$ is *equivalent* to $\lambda=\kappa$ being optimal on $\Theta$, and concludes that $\delta\notin\Delta^\succ$ iff $E_F[u'(x^\mathsf T\kappa)x]^\mathsf T\delta\le0$ for some $(u,\kappa)$. Only the optimality-implies-$D\le0$ half of that equivalence holds: with $u(y)=-e^{-y}$, $x^\mathsf T\kappa\equiv0$ and $x^\mathsf T\delta\in\{2,-1\}$ with probability $\tfrac12$ each, $D<0$ while $E_F[u'(x^\mathsf T\kappa)x^\mathsf T\delta]=\tfrac12>0$. This item poses only the valid KKT equivalence between segment optimality and the first-order condition. The segment is $\theta\in[0,1]$, written with `IsMaxOn` on `Set.Icc 0 1`.
-- source:
--   Arvanitis & Post, Ordering Arbitrage Portfolios and Finding Arbitrage Opportunities, AUEB Department of Economics Working Paper 04-2022 (March 2022; published as Generalized Stochastic Arbitrage Opportunities, Management Science 2024), proof of Theorem 2.3.1, pp. 34–35 (PDF 35–36), 'The necessary and sufficient Karush-Kuhn-Tucker condition therefore implies …'

import Mathlib
import Definitions.Def_StochArbitrage_Pricing_Model

namespace StochArbitrage.Pricing

open MeasureTheory

/-- The valid segment-optimality condition in the proof of Theorem 2.3.1. -/
theorem kkt_segment {N R : ℕ} (M : Market N R) (U : Set (ℝ → ℝ))
    (K : Set (Fin N → ℝ)) (hS : M.Standing U K)
    (u : ℝ → ℝ) (hu : u ∈ U) (κ δ : Fin N → ℝ)
    (hκ : κ ∈ K) (hδ : δ ∈ M.overlaySet) :
    IsMaxOn (fun θ : ℝ => ∫ x, u (x ⬝ᵥ (κ + θ • δ)) ∂M.μ)
      (Set.Icc 0 1) 0 ↔
      M.presentValue (fun x => deriv u (x ⬝ᵥ κ)) ⬝ᵥ δ ≤ 0 := by sorry

end StochArbitrage.Pricing
