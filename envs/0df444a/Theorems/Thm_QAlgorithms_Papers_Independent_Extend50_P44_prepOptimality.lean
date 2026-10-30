-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P44_prepOptimality
-- name    : QAlgorithms.Papers.Independent.Extend50.P44.prepOptimality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:12:46.925679+00:00
-- url     : https://prove2.me/theorems/dd855415-a335-4758-89e5-ec69c0e11ee1
-- title:
--   §2.3: optimal p and comparison to base normalization (33)–(34)
-- statement:
--   Let $D,S_c,S_r>0$ and let $a_0,\ldots,a_{D-1}$ be nonzero real values. Define $\alpha_p$ by (32). For every $p\in[0,1]$,
--   $$ \alpha_{1/2}=\frac{\sqrt{S_cS_r}}D\sum_j|a_j|\le\alpha_p=\alpha_{1-p}\le\sqrt{S_cS_r}\max_j|a_j|. $$
--   Also $\alpha_p\le\alpha_q$ whenever $1/2\le p\le q\le1$. Thus $p=1/2$ is a universal minimizer, without a uniqueness assertion. Constant-magnitude data make the expression independent of $p$. This quantifies the normalization improvement over the base scheme.
-- source:
--   Block-encoding structured matrices for data input in quantum computing, arXiv:2302.10949v2, PDF p. 11, §2.3: optimal p and comparison to base normalization (33)–(34)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P44

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Frontier18.P11 (complexMatrix)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

open QAlgorithms.Papers.Independent.Next46.P21 (tCount)

variable {n s d m : ℕ}

/-- PDF pp.10-11, (33)-(34): symmetry, a universal minimizer, monotonicity
away from one half, and the base-normalization comparison. No uniqueness is claimed. -/
theorem prepOptimality (D Sc Sr : ℕ) (hD : 0 < D) (hc : 0 < Sc) (hr : 0 < Sr)
    (a : Fin D → ℝ) (hnz : ∀ d, a d ≠ 0) :
    prepAlpha a Sc Sr (1 / 2) = Real.sqrt ((Sc : ℝ) * Sr) / D * (∑ d, |a d|) ∧
    (∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      prepAlpha a Sc Sr p = prepAlpha a Sc Sr (1 - p) ∧
      prepAlpha a Sc Sr (1 / 2) ≤ prepAlpha a Sc Sr p ∧
      prepAlpha a Sc Sr p ≤ Real.sqrt ((Sc : ℝ) * Sr) * tableMax a) ∧
    (∀ p q : ℝ, 1 / 2 ≤ p → p ≤ q → q ≤ 1 →
      prepAlpha a Sc Sr p ≤ prepAlpha a Sc Sr q) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P44

end
