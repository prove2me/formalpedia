-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P35_regularization_limit
-- name    : QAlgorithms.Papers.Independent.Dependency50.P35.regularization_limit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:08:55.661186+00:00
-- url     : https://prove2.me/theorems/2f5ea2e9-ed6f-4af9-88c2-96982e981841
-- title:
--   Lemma 13: positive regularization limit
-- statement:
--   Let $X,Y\ge0$ with $X\ne0$, and let $\alpha\in(0,1)\cup(1,\infty)$. For $\xi>0$ define $S_\xi=(Y+\xi I)^{(1-\alpha)/(2\alpha)}$. Then
--
--   $$
--   \lim_{\xi\downarrow0}\frac{\alpha}{\alpha-1}\log_2\left(\frac{\operatorname{Tr}[(S_\xi X S_\xi)^\alpha]}{\operatorname{Tr}X}\right)^{1/\alpha}=\widetilde D_\alpha(X\|Y).
--   $$
--
--   The limit is in the extended real line, including genuine divergence to $+\infty$, as established in the proof on PDF p.16. The exponent applies to the entire ratio; no support-domination assumption is required.
-- source:
--   On quantum Renyi entropies: a new generalization and some properties, arXiv:1306.3142v4, PDF p. 15, Lemma 13

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted matrix type and positive-operator Schatten expression.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

/-- PDF pp.15–16, Lemma 13: the entire trace ratio is raised to 1/a, including
its denominator. Ordinary EReal convergence preserves genuine divergence to +infinity. -/
theorem regularization_limit {I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (ha : 0 < a ∧ a ≠ 1) (X Y : Mat I)
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (hn : X ≠ 0) :
    Tendsto (fun xi : ℝ =>
      ((a/(a-1) * Real.logb 2
        ((rawTrace a X (Y + (xi : ℂ) • (1 : Mat I)) / tr X) ^ (1/a)) : ℝ) : EReal))
      (𝓝[>] 0) (𝓝 (divergence a X Y)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P35

end
