-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_commutingMinimum
-- name    : QAlgorithms.Papers.Independent.Gap48.P40.commutingMinimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:24:34.142983+00:00
-- url     : https://prove2.me/theorems/057cc59f-1c9b-4ce5-b6a1-247193ec9b86
-- title:
--   §VI, Lemma 8: a commuting pair attains the minimum
-- statement:
--   All matrices act on a complex Hilbert space of positive finite dimension $d$. A state is positive semidefinite with trace one. All logarithms are natural, and $D(\rho\|\sigma)$ denotes support-aware Umegaki relative entropy, with value $+\infty$ when support containment fails. Let $N$ be any genuine unitarily invariant norm on $d\times d$ complex matrices. Write $E=\operatorname{diag}(1,0,\ldots)$ and, when $d\ge2$, $F=\operatorname{diag}(1,-1,0,\ldots)$. The symbols $\|\cdot\|_\infty$, $\|\cdot\|_1$ and $\|\cdot\|_2$ mean operator, full trace and Hilbert–Schmidt norms, respectively. For $d\ge2$ and $0\le T\le N(F)$, let $m_N(T)$ be the extended infimum at raw distance $T$. There exist states $\rho,\sigma$, with $\Delta=\rho-\sigma$, such that
--
--   $$
--   N(\Delta)=T,\qquad[\sigma,\Delta]=0,\qquad D(\rho\|\sigma)=m_N(T).
--   $$
--
--   A commuting pair attains the minimum; the statement also includes the infinite endpoint.
-- source:
--   Continuity bounds on the quantum relative entropy, arXiv:quant-ph/0503218v3, PDF p. 6, §VI, Lemma 8: a commuting pair attains the minimum

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open Filter MeasureTheory Asymptotics

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

namespace QAlgorithms.Papers.Independent.Gap48.P40

/-- PDF pp.6–7, Lemma 8: a commuting pair attains the minimum, including infinity. -/
theorem commutingMinimum {d : ℕ} (hd : 2 ≤ d) (N : Mat d → ℝ) (hN : IsUINorm N)
    (T : ℝ) (hT : 0 ≤ T ∧ T ≤ N (matrixF d)) :
    ∃ rho sigma : Mat d, IsDensityMatrix rho ∧ IsDensityMatrix sigma ∧
      N (rho - sigma) = T ∧ sigma * (rho - sigma) = (rho - sigma) * sigma ∧
      relativeEntropy rho sigma = minimumAt d N T := by sorry

end QAlgorithms.Papers.Independent.Gap48.P40

end
