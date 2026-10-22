-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_sharpLowerBound
-- name    : QAlgorithms.Papers.Independent.Gap48.P40.sharpLowerBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:27:06.125075+00:00
-- url     : https://prove2.me/theorems/a0d60ed4-6404-4461-a6f4-35e32af50245
-- title:
--   §VI, Theorem 4: sharp lower bound for every UI norm (seed headline)
-- statement:
--   All matrices act on a complex Hilbert space of positive finite dimension $d$. A state is positive semidefinite with trace one. All logarithms are natural, and $D(\rho\|\sigma)$ denotes support-aware Umegaki relative entropy, with value $+\infty$ when support containment fails. Let $N$ be any genuine unitarily invariant norm on $d\times d$ complex matrices. Write $E=\operatorname{diag}(1,0,\ldots)$ and, when $d\ge2$, $F=\operatorname{diag}(1,-1,0,\ldots)$. The symbols $\|\cdot\|_\infty$, $\|\cdot\|_1$ and $\|\cdot\|_2$ mean operator, full trace and Hilbert–Schmidt norms, respectively. For $0\le x<1$, define $s(x)=\inf_{0<r<1-x}D(\operatorname{diag}(r+x,1-r-x)\|\operatorname{diag}(r,1-r))$, and set $s(1)=+\infty$. For $d\ge2$ and every pair of states,
--
--   $$
--   D(\rho\|\sigma)\ge s\!\left(\frac{N(\rho-\sigma)}{N(F)}\right).
--   $$
--
--   For every $t\in[0,1]$, a pair of commuting states in that same dimension attains equality and has rescaled distance $t$.
--
--   This is the sharp all-UI-norm lower bound, including the orthogonal-state infinite endpoint.
-- source:
--   Continuity bounds on the quantum relative entropy, arXiv:quant-ph/0503218v3, PDF p. 1, §VI, Theorem 4: sharp lower bound for every UI norm (seed headline)

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

/-- PDF pp.7–8, Theorem 4: sharp lower bound for every UI norm, including
attainment at every rescaled distance in every d>=2. Endpoints use extended entropy. -/
theorem sharpLowerBound {d : ℕ} (hd : 2 ≤ d) (N : Mat d → ℝ) (hN : IsUINorm N) :
    (∀ rho sigma : Mat d, IsDensityMatrix rho → IsDensityMatrix sigma →
      binaryProfile (rescaled N (rho - sigma)) ≤ relativeEntropy rho sigma) ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ rho sigma : Mat d,
      IsDensityMatrix rho ∧ IsDensityMatrix sigma ∧
      rescaled N (rho - sigma) = t ∧ rho * sigma = sigma * rho ∧
      relativeEntropy rho sigma = binaryProfile t) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P40

end
