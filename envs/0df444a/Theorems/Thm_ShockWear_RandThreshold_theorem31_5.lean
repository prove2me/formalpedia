-- Prove2me | Theorems.Thm_ShockWear_RandThreshold_theorem31_5
-- name    : ShockWear.RandThreshold.theorem31_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:49:52.70596+00:00
-- url     : https://prove2.me/theorems/b88c41f9-7ff0-4793-8d69-00b8a1bf73bb
-- title:
--   Theorem 3.1 (3.5) — submultiplicative shock survival probabilities give an NBU life distribution
-- statement:
--   Let $\lambda > 0$ and let $\bar P_0, \bar P_1, \dots$ be real numbers with
--   $$1 = \bar P_0 \ge \bar P_1 \ge \bar P_2 \ge \cdots \ge 0 .$$
--   Consider the survival function of a device exposed to shocks arriving as a Poisson process of rate $\lambda$, which survives $k$ shocks with probability $\bar P_k$:
--   $$\bar H(t) = \sum_{k=0}^\infty \bar P_k\, e^{-\lambda t}\frac{(\lambda t)^k}{k!}, \qquad t \ge 0 .$$
--   If the sequence is submultiplicative,
--   $$\bar P_j \bar P_k \ge \bar P_{j+k}, \qquad j, k = 0, 1, \dots,$$
--   then $H$ is NBU (new better than used): $\bar H(t + x) \le \bar H(x)\bar H(t)$ for all $x, t \ge 0$.
--
--   The condition on the $\bar P_k$ is the discrete analogue of the NBU property, and the theorem says it passes from the number of shocks survived to the continuous-time life distribution. It is the step that turns the random-threshold characterization of Theorem 5.3 into a statement about the life distribution $H$.
--
--   **Formalization Note.** The paper's sequence satisfies $1 = \bar P_0 \ge \bar P_1 \ge \cdots$; the non-negativity $\bar P_k \ge 0$ (they are probabilities) is stated explicitly, as is $\lambda > 0$ from (1.1). NBU is stated in the cross-multiplied form $\bar H(t+x) \le \bar H(x)\bar H(t)$ of definition (v).
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 632, Theorem 3.1 (3.5)

import Mathlib
import Definitions.Def_ShockWear_RandThreshold_Model

namespace ShockWear.RandThreshold

open MeasureTheory ProbabilityTheory

theorem theorem31_5 (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ) (hP0 : P 0 = 1)
    (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (hsub : ∀ j k, P (j + k) ≤ P j * P k) :
    IsNBU (shockSurv lam P) := by sorry

end ShockWear.RandThreshold
