-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_smallDistanceEquality
-- name    : QAlgorithms.Papers.Independent.Gap48.P40.smallDistanceEquality
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:31:32.064877+00:00
-- url     : https://prove2.me/theorems/b93284ed-03ef-4450-873f-3300f8092369
-- title:
--   §VII.B, explicit small-distance equality construction
-- statement:
--   Let $d\ge3$, $0<\beta\le1/d$ and $0\le T\le\beta$. With $e_3$ the third basis vector and $F=\operatorname{diag}(1,-1,0,\ldots)$, define $\sigma=\beta I+(1-d\beta)|e_3\rangle\langle e_3|$ and $\rho=\sigma+TF$. These are states, their reference minimum eigenvalue is $\beta$, and
--
--   $$
--   \frac12\|\rho-\sigma\|_1=T,\qquad D(\rho\|\sigma)=(\beta+T)\log\frac{\beta+T}{\beta}+(\beta-T)\log\frac{\beta-T}{\beta}.
--   $$
--
--   This attains the small-distance upper bound in each fixed dimension at least three, including its boundary values.
-- source:
--   Continuity bounds on the quantum relative entropy, arXiv:quant-ph/0503218v3, PDF p. 11, §VII.B, explicit small-distance equality construction

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

/-- PDF p.11: the source's explicit small-distance equality construction,
with third coordinate distinct from the first two and the actual minimum beta. -/
theorem smallDistanceEquality {d : ℕ} (hd : 3 ≤ d) (beta T : ℝ)
    (hbeta : 0 < beta ∧ beta ≤ 1 / (d : ℝ)) (hT : 0 ≤ T ∧ T ≤ beta) :
    IsDensityMatrix (smallRho d beta T) ∧ IsDensityMatrix (smallSigma d beta) ∧
    minEigenvalue (smallSigma d beta) = beta ∧
    traceNorm (smallRho d beta T - smallSigma d beta) / 2 = T ∧
    relativeEntropy (smallRho d beta T) (smallSigma d beta) =
      ((traceSmallBound beta T : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P40

end
