-- Prove2me | Theorems.Thm_RobustSpecClust_Est_eq_E5
-- name    : RobustSpecClust.Est.eq_E5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:33.525569+00:00
-- url     : https://prove2.me/theorems/44dfdf0f-071f-4a93-8a05-712469b318bd
-- title:
--   (E.5), p. 40 — the difference of independent sub-gaussian vectors with parameters ≤ σ̄ is sub-gaussian with parameter √2σ̄
-- statement:
--   Let $\xi$ and $\xi'$ be independent random vectors in $\mathbb R^d$ on a probability space, sub-gaussian (Definition 3, mean zero) with parameters $s$ and $s'$, and let $\bar\sigma \ge \max\{s, s'\}$. Then $\xi - \xi'$ is sub-gaussian with parameter $\sqrt 2\,\bar\sigma$: for every $c \in \mathbb R^d$,
--   $$\mathbb E\big[\exp(c^\top(\xi - \xi'))\big] \le \exp\Big(\frac{\|c\|^2\, 2\bar\sigma^2}{2}\Big).$$
--
--   In the paper this is applied to $\xi_i - \xi_j$ with $\bar\sigma = \sigma_{\max}$; it is the input to the quadratic-form tail (E.6) and the linear tail (E.9).
--
--   **Formalization Note** Definition 3 is encoded as Mathlib's `HasSubgaussianMGF` of every projection $\nu^\top\xi$, which includes integrability of the exponential moments.
-- source:
--   arXiv:1912.07546v3, Appendix E, display (E.5), p. 40

import Mathlib
import Definitions.Def_RobustSpecClust_Est_Setting
open MeasureTheory ProbabilityTheory

namespace RobustSpecClust.Est

theorem eq_E5 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ ξ' : Ω → E d) (s s' σbar : ℝ) (hind : IndepFun ξ ξ' P)
    (hξ : IsSubgaussianVec P ξ s) (hξ' : IsSubgaussianVec P ξ' s')
    (hs : s ≤ σbar) (hs' : s' ≤ σbar) :
    IsSubgaussianVec P (ξ - ξ') (Real.sqrt 2 * σbar) := by sorry

end RobustSpecClust.Est
