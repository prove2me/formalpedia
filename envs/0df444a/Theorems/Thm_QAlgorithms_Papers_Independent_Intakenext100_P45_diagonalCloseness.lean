-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_diagonalCloseness
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.diagonalCloseness
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:08:08.908675+00:00
-- url     : https://prove2.me/theorems/387afd8f-0e59-4f11-866b-65d4011c36b2
-- title:
--   §4.7, closeness near the diagonal
-- statement:
--   Let $Q$ and $\xi=-\log Q$ be the Chernoff coefficient and extended distance, and let $T$ be trace distance. Then
--
--   $$0\le1-Q\le T,\qquad T<1\Longrightarrow\xi\le-\log(1-T).$$
--
--   There are positive constants $C,\delta$ with $\delta<1$ such that $|{-\log(1-t)}-t|\le Ct^2$ for $0\le t<\delta$. Thus trace-distance closeness forces Chernoff closeness near the diagonal; no finite-valued continuity claim at orthogonal pairs is made.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 19, §4.7, closeness near the diagonal

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

/-- arXiv:0708.4282v1, PDF p.19: §4.7, closeness near the diagonal. -/
theorem diagonalCloseness :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta < 1 ∧
      (∀ t : ℝ, 0 ≤ t → t < delta → abs (-Real.log (1-t)-t) ≤ C*t^2) ∧
      ∀ {K : Type} [Fintype K] [DecidableEq K] (rho sigma : Mat K),
        IsDensityMatrix rho → IsDensityMatrix sigma →
        0 ≤ 1-chernoffInfimum rho sigma ∧ 1-chernoffInfimum rho sigma ≤ traceDist rho sigma ∧
        (traceDist rho sigma < 1 →
          chernoffDistance rho sigma ≤ ((-Real.log (1-traceDist rho sigma) : ℝ) : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
