-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_traceBoundSharpness
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.traceBoundSharpness
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:02:25.801996+00:00
-- url     : https://prove2.me/theorems/d5272f9e-4429-4d48-89d3-0237042d8347
-- title:
--   Unnumbered sharpness of 1-T<=Q
-- statement:
--   For every $T\in[0,1]$, take the commuting qubit densities $\rho=\operatorname{diag}(1,0)$ and $\sigma=\operatorname{diag}(1-T,T)$. Then
--
--   $$\tfrac12\|\rho-\sigma\|_1=T,\qquad Q(\rho,\sigma)=1-T.$$
--
--   Thus the bound $Q+T\ge1$ is sharp for every allowed trace distance. The printed fixed-$s$ equality is corrected: for $0<s<1$, the example has $Q_s=(1-T)^s$; the infimum is obtained as $s\uparrow1$ when $0<T<1$.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 13, Unnumbered sharpness of 1-T<=Q

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

/-- arXiv:0708.4282v1, PDF p.13: Unnumbered sharpness of 1-T<=Q. Source correction: PDF p.13 prints Qs=1-T; changed to the infimum Q=1-T, since the example gives Qs=(1-T)^s in the open interval. Independent moderation required. -/
theorem traceBoundSharpness (T : ℝ) (h0 : 0 ≤ T) (h1 : T ≤ 1) :
    let rho : Mat (Fin 2) := Matrix.diagonal ![1,0]
    let sigma : Mat (Fin 2) := Matrix.diagonal ![((1-T : ℝ) : ℂ),(T : ℂ)]
    IsDensityMatrix rho ∧ IsDensityMatrix sigma ∧
    traceDist rho sigma = T ∧ chernoffInfimum rho sigma = 1-T := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
