-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_figure10_two_measurements
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P52.figure10_two_measurements
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:43:46.861538+00:00
-- url     : https://prove2.me/theorems/18615c00-7b66-4899-a919-21c3a585373a
-- title:
--   §6.1 Figure 10: two-step x rotation
-- statement:
--   Let $\theta$ be real and let $|\psi\rangle$ have unit norm. Entangle $|\psi\rangle|+\rangle|+\rangle$ as a three-site line. Measure site $1$ in $X$ and site $2$ in $M(-2\theta)$, with outcomes $s_1,s_2$. The branch $b_s$ has probability $1/4$ and
--
--   $$ |b_s\rangle\langle b_s|=\tfrac14|\chi_s\rangle\langle\chi_s|,\qquad |\chi_s\rangle=X^{s_2}Z^{s_1}R_x((-1)^{s_1}\theta)|\psi\rangle. $$
--
--   Choosing the second basis adaptively as $M(-2(-1)^{s_1}\theta)$ instead gives $|\chi_s\rangle=X^{s_2}Z^{s_1}R_x(\theta)|\psi\rangle$, again with probability $1/4$. **Source correction:** the drawn $M(-\theta)$ yields half the caption's rotation under the p.5 convention, so the measurement angle is doubled.
-- source:
--   An introduction to measurement based quantum computation, arXiv:quant-ph/0508124v2, PDF p. 13, §6.1 Figure 10: two-step x rotation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P52

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Figure 10, PDF p.13. Printed M(-theta) gives Rx(theta/2); changed to
M(-2theta) to retain the caption's Rx((-1)^s1 theta) target. The second
conjunct gives the causal sign adaptation for a prescribed Rx(theta). -/
theorem figure10_two_measurements (theta : ℝ) (psi : Vec Bool)
    (hpsi : IsState psi) (s : Fin 2 → Bool) :
    (let b := lineBranch 2 ![0,-2*theta] s psi
     pureDensity b = (1 / 4 : ℝ) •
       pureDensity (act (pauliByproduct (s 1) (s 0) * rx (angleSign (s 0) * theta)) psi) ∧
     ‖b‖ ^ 2 = (1 / 4 : ℝ)) ∧
    (let b := lineBranch 2 ![0,-2*angleSign (s 0)*theta] s psi
     pureDensity b = (1 / 4 : ℝ) • pureDensity (act (pauliByproduct (s 1) (s 0) * rx theta) psi) ∧
     ‖b‖ ^ 2 = (1 / 4 : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P52

end
