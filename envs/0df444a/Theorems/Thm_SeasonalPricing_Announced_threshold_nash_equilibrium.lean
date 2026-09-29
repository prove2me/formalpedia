-- Prove2me | Theorems.Thm_SeasonalPricing_Announced_threshold_nash_equilibrium
-- name    : SeasonalPricing.Announced.threshold_nash_equilibrium
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:13:48.28944+00:00
-- url     : https://prove2.me/theorems/ebb29009-3403-4a00-b365-9322b55b7ee3
-- title:
--   Theorem 2: under an announced price path, the threshold $\psi_A$ with availability $w$ solving (8) is a Nash equilibrium
-- statement:
--   Consider the model of Aviv and Pazgal: $Q \ge 1$ units, Poisson arrivals with rate $\lambda > 0$, base valuations with a continuous distribution $F$, valuations $V(t) = Ve^{-\alpha t}$ with $\alpha \ge 0$, discount time $T > 0$, and an announced price path $(p_1, p_2)$ with $p_2 \le p_1$. Let $w \in [0, 1]$ be a solution of Eq. (8),
--
--   $$
--   w = \sum_{x=0}^{Q-1} P\big(x \mid \Lambda_I(\psi_A)\big)\cdot A\big(Q - x \mid \Lambda_S(\psi_A, p_1, p_2) + \Lambda_W(p_1, p_2)\big),
--   $$
--
--   where $\psi_A(t) = \max\{p_1, (p_1 - wp_2)/(1 - we^{-\alpha(T-t)})\}$ is the threshold of Eq. (7), and assume $\alpha > 0$ or $w < 1$. Then, when every other customer follows the threshold $\psi_A$, so that a waiting customer is allocated a unit at time $T$ with the probability given by the right-hand side of (8), a customer arriving at any $t \in [0, T)$ with any base valuation $V$ buys immediately (current surplus nonnegative and at least the expected surplus of waiting) if and only if
--
--   $$
--   V(t) \ge \psi_A(t).
--   $$
--
--   That is, the threshold policy $\psi_A$ is a best response to itself: the symmetric threshold profile of Eq. (7) is a Nash equilibrium of the customers' purchasing game on $[0, T)$.
--
--   The theorem is the announced-pricing counterpart of the paper's Theorem 1, and it is the input to the seller's revenue $\pi_{A/S}(p_1, p_2)$ on p. 348 and the comparison of announced and contingent pricing in §7.3.
--
--   **Formalization Note** "Nash equilibrium" is read as the best-response property that the paper's proof checks: the availability a customer faces is the right-hand side of (8) evaluated at $w$, and against it the immediate-purchase rule coincides with the threshold $\psi_A$. The paper assumes a solution $w$ of (8) exists and does not prove it; the theorem is conditional on one. The hypotheses $0 \le w \le 1$ read $w$ as a likelihood, as the paper does. The hypothesis "$\alpha > 0$ or $w < 1$" is an addition that keeps $1 - we^{-\alpha(T-t)}$ positive for $t < T$. The rule on $[T, H]$ (buy at time $T$ iff $V(T) > p_2$) is part of the model and not restated; the horizon $H$ does not enter the statement. Continuity of $F$ is the paper's standing assumption and is carried as a hypothesis; no sign restriction on $V$ is imposed.
-- source:
--   Aviv and Pazgal, Optimal Pricing of Seasonal Products in the Presence of Forward-Looking Consumers, Manufacturing & Service Operations Management 10(3), 2008, p. 348, Theorem 2, Eqs. (7)–(8); p. 358, Proof of Theorem 2

import Mathlib
import Definitions.Def_SeasonalPricing_Announced_availability

namespace SeasonalPricing.Announced

open MeasureTheory

theorem threshold_nash_equilibrium (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hF : Continuous (ProbabilityTheory.cdf μ))
    (lam α T : ℝ) (Q : ℕ) (p1 p2 w : ℝ)
    (hlam : 0 < lam) (hα : 0 ≤ α) (hT : 0 < T) (hQ : 1 ≤ Q) (hp : p2 ≤ p1)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hdeg : 0 < α ∨ w < 1)
    (h8 : w = availability μ lam α T Q p1 p2 w) :
    ∀ t : ℝ, 0 ≤ t → t < T → ∀ V : ℝ,
      buysNow α T p1 p2 (availability μ lam α T Q p1 p2 w) t V ↔
        psiA α T p1 p2 w t ≤ valuation α V t := by sorry

end SeasonalPricing.Announced
