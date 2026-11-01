-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_fidelityBounds
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.fidelityBounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:03:03.037978+00:00
-- url     : https://prove2.me/theorems/48bb2fbb-585d-419f-85fb-7ad1388de34b
-- title:
--   §4.1, fidelity and trace-distance bounds (28)–(32)
-- statement:
--   For finite-dimensional densities $\rho,\sigma$, put $Q=\inf_{0\le s\le1}\operatorname{Tr}(\rho^{1-s}\sigma^s)$, $T=\|\rho-\sigma\|_1/2$, and use the unsquared fidelity $F=\|\rho^{1/2}\sigma^{1/2}\|_1$. The complete bounds are
--
--   $$Q\le\operatorname{Tr}(\rho^{1/2}\sigma^{1/2})=\|\rho^{1/4}\sigma^{1/2}\rho^{1/4}\|_1\le F,$$
--   $$(1-F)^2\le T^2\le1-F^2,\qquad Q^2+T^2\le1,$$
--   $$1-\sqrt{1-F^2}\le1-T\le Q\le F\le\sqrt{1-T^2},\qquad F^2\le Q.$$
--
--   If either state is pure, $Q=F^2$. These compare the operational Chernoff coefficient with standard state distinguishability measures.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 16, §4.1, fidelity and trace-distance bounds (28)–(32)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P45

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P45

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal BigOperators Topology

open QAlgorithms.Papers.Independent.Information100.P07
  (support positivePart positiveProjection IsProjection)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Dependency50.P28 (logNonnegativeExtended relativeEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P15 (positiveMatrixRpow)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:0708.4282v1, PDF pp.16,17: §4.1, fidelity and trace-distance bounds (28)–(32). -/
theorem fidelityBounds (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    let Q := chernoffInfimum rho sigma
    let F := rootFidelity rho sigma
    let T := traceDist rho sigma
    Q ≤ (positiveMatrixRpow rho (1/2) * positiveMatrixRpow sigma (1/2)).trace.re ∧
    (positiveMatrixRpow rho (1/2) * positiveMatrixRpow sigma (1/2)).trace.re =
      traceNorm (positiveMatrixRpow rho (1/4) * positiveMatrixRpow sigma (1/2) * positiveMatrixRpow rho (1/4)) ∧
    traceNorm (positiveMatrixRpow rho (1/4) * positiveMatrixRpow sigma (1/2) * positiveMatrixRpow rho (1/4)) ≤
      traceNorm (positiveMatrixRpow rho (1/2) * positiveMatrixRpow sigma (1/2)) ∧
    traceNorm (positiveMatrixRpow rho (1/2) * positiveMatrixRpow sigma (1/2)) = F ∧
    (1-F)^2 ≤ T^2 ∧ T^2 ≤ 1-F^2 ∧ Q^2+T^2 ≤ 1 ∧
    1-Real.sqrt (1-F^2) ≤ 1-T ∧ 1-T ≤ Q ∧ Q ≤ F ∧
    F ≤ Real.sqrt (1-T^2) ∧ F^2 ≤ Q ∧
    ((densityIdempotence rho ∨ densityIdempotence sigma) → Q=F^2) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
