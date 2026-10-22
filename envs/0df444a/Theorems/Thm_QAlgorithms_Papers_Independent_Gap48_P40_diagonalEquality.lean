-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_diagonalEquality
-- name    : QAlgorithms.Papers.Independent.Gap48.P40.diagonalEquality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:32:05.661597+00:00
-- url     : https://prove2.me/theorems/38667b97-9348-4d46-94ef-8859c0966970
-- title:
--   §VII.B, explicit diagonal equality construction (54)
-- statement:
--   Let $d\ge3$, $0\le J\le d-3$ be an integer, $K=d-3-J$, and $\beta>0$. Set $\eta=1-T-(d-1-J)\beta$ and assume $\eta\ge0$ and $(J+1)\beta\le T$. Define
--
--   $$
--   \rho=\operatorname{diag}(T+\beta,0,0^{\times J},\beta^{\times K},\beta+\eta),\qquad\sigma=\operatorname{diag}(\beta,T-J\beta,\beta^{\times J},\beta^{\times K},\beta+\eta).
--   $$
--
--   These are states and satisfy $\lambda_{\min}(\sigma)=\beta$, $\|\rho-\sigma\|_1=2T$, and
--
--   $$
--   D(\rho\|\sigma)=(T+\beta)\log((T+\beta)/\beta).
--   $$
--
--   This is the source diagonal equality witness on a corrected domain. The printed condition $Jeta\le T$ only guarantees positivity; the added residual condition is required to preserve the designated minimum eigenvalue. Independent moderation of this correction is pending.
-- source:
--   Continuity bounds on the quantum relative entropy, arXiv:quant-ph/0503218v3, PDF p. 12, §VII.B, explicit diagonal equality construction (54)

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

/-- PDF p.12, Eq.(54), DOMAIN CORRECTION: the printed J beta<=T merely
ensures PSD. Requiring (J+1) beta<=T also makes the residual eigenvalue >=beta,
as required for the designated actual minimum. eta>=0 and K=d-3-J are retained.
This corrected-domain witness does not assert the deferred full sharpness clause. -/
theorem diagonalEquality {d : ℕ} (hd : 3 ≤ d) (J : ℕ) (hJ : J ≤ d - 3)
    (beta T : ℝ) (hbeta : 0 < beta)
    (hresidual : ((J : ℝ) + 1) * beta ≤ T) (heta : 0 ≤ largeEta d J beta T) :
    IsDensityMatrix (largeRho d J beta T) ∧ IsDensityMatrix (largeSigma d J beta T) ∧
    minEigenvalue (largeSigma d J beta T) = beta ∧
    traceNorm (largeRho d J beta T - largeSigma d J beta T) = 2 * T ∧
    relativeEntropy (largeRho d J beta T) (largeSigma d J beta T) =
      (((T + beta) * Real.log ((T + beta) / beta) : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P40

end
