-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_quadraticUpperBound
-- name    : QAlgorithms.Papers.Independent.Gap48.P40.quadraticUpperBound
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:21:27.934932+00:00
-- url     : https://prove2.me/theorems/25fc03af-4011-41a0-9774-ad9e822f50ae
-- title:
--   §V.A, Theorem 2: quadratic Hilbert-Schmidt upper bound
-- statement:
--   All matrices act on a complex Hilbert space of positive finite dimension $d$. A state is positive semidefinite with trace one. All logarithms are natural, and $D(\rho\|\sigma)$ denotes support-aware Umegaki relative entropy, with value $+\infty$ when support containment fails. If $\rho,\sigma$ are states and $\beta=\lambda_{\min}(\sigma)>0$, then
--
--   $$
--   D(\rho\|\sigma)\le\frac{\|\rho-\sigma\|_2^2}{\beta}.
--   $$
--
--   Here $\|\cdot\|_2$ is the Hilbert–Schmidt norm.
--
--   This is a quadratic continuity bound at a full-rank reference state.
-- source:
--   Continuity bounds on the quantum relative entropy, arXiv:quant-ph/0503218v3, PDF p. 5, §V.A, Theorem 2: quadratic Hilbert-Schmidt upper bound

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

/-- PDF p.5, Theorem 2: Schatten-2 (Hilbert–Schmidt) quadratic bound. -/
theorem quadraticUpperBound {d : ℕ} (hd : 0 < d) (rho sigma : Mat d)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hbeta : 0 < minEigenvalue sigma) :
    relativeEntropy rho sigma ≤
      ((frobNorm (rho - sigma) ^ 2 / minEigenvalue sigma : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P40

end
