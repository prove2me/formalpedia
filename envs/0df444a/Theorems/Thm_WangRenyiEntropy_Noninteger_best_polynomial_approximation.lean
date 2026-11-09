-- Prove2me | Theorems.Thm_WangRenyiEntropy_Noninteger_best_polynomial_approximation
-- name    : WangRenyiEntropy.Noninteger.best_polynomial_approximation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:29.823761+00:00
-- url     : https://prove2.me/theorems/0b61d3c5-ab17-4227-9591-891687fb3240
-- title:
--   Lemma 2.2 — uniform power approximation and coefficient bounds
-- statement:
--   For each positive noninteger real $\alpha$, best uniform approximating polynomials to $x^\alpha$ on $[0,1]$ exist at every integer degree bound $k\ge1$. There is one constant $c_\alpha\ge1$, depending only on $\alpha$, such that every best approximant $Q_k(x)=\sum_{j=0}^k a_jx^j$ satisfies
--   $$\|Q_k-x^\alpha\|_{\infty,[0,1]}\le c_\alpha k^{-2\alpha},\qquad \sum_{j=0}^k|a_j|\le c_\alpha8^k.$$
--   Both bounds use the same constant uniformly in $k$ and the choice of minimizer. This gives the approximation and coefficient control required by the concrete estimator, separately from the existence of a best approximant.
--
--   Differences from the source:
--   - encoding: best degree-k polynomial and its uniform error → degree at most k, a minimizer among every such polynomial, and the real supremum on [0,1]; reason: the proof explicitly takes k ≥ 1; continuity for positive α makes the nonempty real supremum bounded
--   - encoding: let Qk be a best approximation polynomial → existence of such a minimizer is explicit, alongside the one uniform constant; reason: the source uses the best approximant at every positive degree, so existence is made explicit without assuming its bounds
-- source:
--   Qisheng Wang, STOC 2027 submission #447 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/447.pdf, printed 6 / PDF 8, Lemma 2.2

import Mathlib
import Definitions.Def_WangRenyiEntropy_Noninteger_SamplingExperiment
import Definitions.Def_WangRenyiEntropy_Noninteger_Approximation

namespace WangRenyiEntropy.Noninteger

/-- Lemma 2.2, printed p.6 / PDF p.8. Best approximants exist; neither their
existence nor their error/coefficient bounds are hypotheses of this item. -/
theorem best_polynomial_approximation (α : ℝ) (hα : NonintegerOrder α) :
    (∀ k : ℕ, 1 ≤ k → ∃ Q : Polynomial ℝ, IsBestApproximation α k Q) ∧
    ∃ c : ℝ, ApproximationConstant α c := by sorry

end WangRenyiEntropy.Noninteger
