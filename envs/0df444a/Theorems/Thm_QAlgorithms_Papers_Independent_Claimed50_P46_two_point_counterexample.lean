-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P46_two_point_counterexample
-- name    : QAlgorithms.Papers.Independent.Claimed50.P46.two_point_counterexample
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:27:59.374839+00:00
-- url     : https://prove2.me/theorems/d244260f-952d-43ef-8960-97b951086b3c
-- title:
--   Example 3: counterexample to unconditional Han formula (86)–(87)
-- statement:
--   Let $b_n>0$ tend to $+\infty$ and let $c>0$. On $\{x_0,x_1\}$, put $\rho_n=(e^{-nb_n},1-e^{-nb_n})$, $\sigma_n=(e^{-nc},1-e^{-nc})$. Use the strict likelihood test. Define $\eta_L,\zeta_U^c$ and $B_e^*$ as in Section VII, and $H_r=\inf_a(a+\max\{\eta_L(a),r\})$.
--
--   For every real $a$, the finite-block type-I and complementary type-II exponents converge, respectively, to
--   $$
--   \eta(a)=\begin{cases}0&a>0,\\+\infty&a\le0,\end{cases}\qquad
--   \zeta^c(a)=\begin{cases}0&a>0,\\c&a\le0.\end{cases}
--   $$
--   The reversed spectral inf- and sup-divergence rates both equal zero. For every real $r$,
--   $$
--   B_e^*(r)=\min\{\max\{r,0\},c\},\qquad H_r=\max\{r,0\}.
--   $$
--   The plateau height and its validity threshold both equal $c$, so condition (80) is precisely $r\le c$.
--
--   This is the counterexample to the unconditional use of the ordinary-limit Han expression.
-- source:
--   An Information-Spectrum Approach to Classical and Quantum Hypothesis Testing for Simple Hypotheses, arXiv:quant-ph/0206185v2, PDF p. 16, Example 3: counterexample to unconditional Han formula (86)–(87)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P46

noncomputable section

open Filter

open scoped BigOperators ENNReal NNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsPositive State relativeEntropy)

universe u

namespace QAlgorithms.Papers.Independent.Claimed50.P46

/-- Example 3, PDF p.16: full counterexample, including spectral limits,
reversed divergence rates, both distinct curves, and their exact validity cutoff. -/
theorem two_point_counterexample (b : ℕ → ℝ) (c : ℝ)
    (hb : ∀ k, 0 < b k) (hbinfty : Tendsto b atTop atTop) (hc : 0 < c) :
    let C := twoPointData b c
    let P := fun k => SimpleHypothesisSystem.classical (C k)
    let S := strictClassicalFamily C
    let R := strictClassicalFamily (fun k => reverseClassical (C k))
    (∀ a : ℝ, Tendsto (fun k => blockErrorExponent k (testingTypeI (S.tests a k))) atTop
        (nhds (if 0 < a then (0 : EReal) else ⊤)) ∧
      Tendsto (fun k => blockErrorExponent k (testingTypeII (testRejection (S.tests a k)))) atTop
        (nhds (if 0 < a then (0 : EReal) else (c : EReal)))) ∧
    divergenceL R 0 = 0 ∧ divergenceU R 1 = 0 ∧
    (∀ r : ℝ, correctTradeoff P true false r = ((min (max r 0) c : ℝ) : EReal) ∧
      hanExpression (fun a => etaL (S.tests a)) r = ((max r 0 : ℝ) : EReal)) ∧
    plateauHeight (fun a => zetaUc (S.tests a)) = (c : EReal) ∧
    plateauThreshold (fun a => zetaUc (S.tests a)) = (c : EReal) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P46

end
