-- Prove2me | Theorems.Thm_UnconditionalKLS_Dunkl_theorem_2_1
-- name    : UnconditionalKLS.Dunkl.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T20:08:32.572179+00:00
-- url     : https://prove2.me/theorems/e983479c-380a-4aba-9df3-ecd6d1b8fd32
-- title:
--   Theorem 2.1 — spectral-gap dichotomy
-- statement:
--   There is a single universal constant $c_*>0$ such that the following holds for every $n\ge1$, every $S>0$, and every unconditional $C^2$ potential $W$ satisfying (2.4). Let $\eta$ be the normalized density proportional to $e^{-W(x)}\prod_jq_S(|x_j|)$ and let $a=\|\operatorname{Cov}(\eta)\|_{\mathrm{op}}$. Its normalizing integral is positive and finite, it is a probability law with finite second moments, and
--   $$C_P(\eta)<\infty,\qquad a\le S^2\Longrightarrow\left(C_P(\eta)>\frac{S^2}{3}\quad\text{or}\quad C_P(\eta)\le\frac{9a}{c_*}\right).$$
--   This is the auxiliary dichotomy for the generally non-log-concave weighted law. The constant is chosen before the dimension, scale and potential; no strong-convexity constant enters the bound. The printed existential constant is retained without numerical instantiation.
--
--   Differences from the source:
--   - encoding: functions on real Euclidean space with the paper’s analytic domains → Fin n coordinates, L² equivalence classes and canonical graph/form completions; extended nonnegative infima; reason: these represent the same objects; positive dimensions are retained and finite integrals are guarded
--   - encoding: the normalized probability law and covariance of (3.2) → positivity and finiteness of the normalizer, probability mass and finite second moment asserted as conclusions; reason: these follow from (2.4); they guard normalization and covariance defaults without adding hypotheses
-- source:
--   Pierre Bizeul, Dan Mikulincer, Ilias Zadik, STOC 2027 submission #1161 (October 2026), p. 9, Theorem 2.1; contextual domains in Appendix A, pp. 31–38. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1161.pdf

import Definitions.Def_UnconditionalKLS_Dunkl_Domains

open MeasureTheory Filter
open scoped BigOperators ENNReal ContDiff
noncomputable section

namespace UnconditionalKLS.Dunkl
theorem theorem_2_1 :
    ∃ cstar : ℝ, 0 < cstar ∧ ∀ (n : ℕ), 0 < n → ∀ (S : ℝ) (W : Fn n),
      0 < S → Admissible W →
      0 < normalizer S W ∧ normalizer S W < ⊤ ∧ IsProbabilityMeasure (eta S W) ∧
      MemLp id 2 (eta S W) ∧ poincare (eta S W) < ⊤ ∧
      (covNorm (eta S W) ≤ S^2 →
        ENNReal.ofReal (S^2/3) < poincare (eta S W) ∨
        poincare (eta S W) ≤ ENNReal.ofReal (9 * covNorm (eta S W) / cstar)) := by sorry
end UnconditionalKLS.Dunkl
