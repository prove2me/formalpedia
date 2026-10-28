-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_qubitUpperBound
-- name    : QAlgorithms.Papers.Independent.Gap48.P40.qubitUpperBound
-- status  : Disproved
-- author  : @Goku
-- created : 2026-10-22T05:28:53.208909+00:00
-- url     : https://prove2.me/theorems/0a6cd6c8-4456-4fb1-90a3-64247cdbf093
-- title:
--   §VII.A, Theorem 5: two-regime qubit upper bound
-- statement:
--   All matrices act on a complex Hilbert space of positive finite dimension $d$. A state is positive semidefinite with trace one. All logarithms are natural, and $D(\rho\|\sigma)$ denotes support-aware Umegaki relative entropy, with value $+\infty$ when support containment fails. Let $N$ be any genuine unitarily invariant norm on $d\times d$ complex matrices. Write $E=\operatorname{diag}(1,0,\ldots)$ and, when $d\ge2$, $F=\operatorname{diag}(1,-1,0,\ldots)$. The symbols $\|\cdot\|_\infty$, $\|\cdot\|_1$ and $\|\cdot\|_2$ mean operator, full trace and Hilbert–Schmidt norms, respectively. For qubit states, put $\beta=\lambda_{\min}(\sigma)>0$ and $T=N(\rho-\sigma)/N(F)$. If $T\le\beta$,
--
--   $$
--   D(\rho\|\sigma)\le (T+1-\beta)\log\frac{T+1-\beta}{1-\beta}+(\beta-T)\log(1-T/\beta).
--   $$
--
--   If $T>\beta$,
--
--   $$
--   D(\rho\|\sigma)\le\max\!\left\{-\log(1-T),(\beta+T)\log(1+T/\beta)+(1-\beta-T)\log(1-T/(1-\beta))\right\}.
--   $$
--
--   All zero-weight logarithmic terms use their continuous value zero.
--
--   The complete two-regime inequality is retained without a fixed-beta optimality assertion.
-- source:
--   Continuity bounds on the quantum relative entropy, arXiv:quant-ph/0503218v3, PDF p. 10, §VII.A, Theorem 5: two-regime qubit upper bound

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

/-- PDF p.10, Theorem 5: both qubit regimes; no unsupported fixed-beta equality clause. -/
theorem qubitUpperBound (N : Mat 2 → ℝ) (hN : IsUINorm N) (rho sigma : Mat 2)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hbeta : 0 < minEigenvalue sigma) :
    let beta := minEigenvalue sigma
    let T := rescaled N (rho - sigma)
    (T ≤ beta → relativeEntropy rho sigma ≤ ((qubitSmallBound beta T : ℝ) : EReal)) ∧
    (beta < T → relativeEntropy rho sigma ≤ ((qubitLargeBound beta T : ℝ) : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P40

end
