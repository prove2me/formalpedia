-- Prove2me | Theorems.Thm_QiFixedDesign_Concentration_lemma_3
-- name    : QiFixedDesign.Concentration.lemma_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:59:49.426891+00:00
-- url     : https://prove2.me/theorems/1d72612c-dee6-429a-9434-566e045f8e17
-- title:
--   Lemma 3 — leverage bounds and the full trace identity
-- statement:
--   For a real $N\times p$ design matrix $X$ with nonsingular $X^T X$, set $H=X(X^TX)^{-1}X^T$. Then both assertions hold:
--   $$0\le H_{ii}\le1\quad(1\le i\le N),\qquad \operatorname{trace}(H)=\sum_{i=1}^N H_{ii}=p.$$
--   Full rank is the standing Assumption 1. The trace and each individual leverage bound are retained. Empty-dimensional matrices are included under the same nonsingularity guard; the trace identity still applies.
--
--   Differences from the source:
--   - encoding: coordinates and samples numbered from one → Fin p and Fin N numbered from zero, with natural-number dimension p; reason: the coordinate bijections preserve all sums and matrices; zero dimensions are not silently excluded
--   - encoding: Assumption 1 gives full column rank → the Gram determinant is nonzero; reason: over real finite matrices this is equivalent to full column rank
--   - generalization: the Section 3 model has no intercept term → the deterministic design may include constant feature columns; reason: the OLS and concentration statements use full column rank and the Gram limit, not exclusion of constant columns; every source design is included with the same conclusions
-- source:
--   Qi, Cao and Shen (2021), Distributionally Robust Conditional Quantile Prediction with Fixed Design, DOI 10.1287/mnsc.2020.3903, supplied source.pdf, Lemma 3, (19), PDF/printed p. 13

import Mathlib
import Definitions.Def_QiFixedDesign_Concentration_Hat

open MeasureTheory Matrix Filter Topology
open scoped ENNReal

namespace QiFixedDesign.Concentration

theorem lemma_3 {N p : ℕ} (X : Matrix (Fin N) (Fin p) ℝ)
    (hX : (X.transpose * X).det ≠ 0) :
    (∀ i : Fin N, 0 ≤ hat X i i ∧ hat X i i ≤ 1) ∧
    Matrix.trace (hat X) = ∑ i : Fin N, hat X i i ∧
    (∑ i : Fin N, hat X i i) = (p : ℝ) := by sorry

end QiFixedDesign.Concentration
