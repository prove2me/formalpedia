-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_triangleFailure
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.triangleFailure
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:04:34.515227+00:00
-- url     : https://prove2.me/theorems/236cf09d-560c-44f6-93b1-20cc44763c19
-- title:
--   §4.3, triangle-inequality failure
-- statement:
--   For Bernoulli laws $p_\varepsilon=(\varepsilon,1-\varepsilon)$, $q_\varepsilon=(1-\varepsilon,\varepsilon)$ and $u=(1/2,1/2)$, there is $\delta\in(0,1/2]$ such that every $0<\varepsilon<\delta$ gives finite Chernoff distances and
--
--   $$\sqrt{\xi(p_\varepsilon,q_\varepsilon)}>\sqrt{\xi(p_\varepsilon,u)}+\sqrt{\xi(u,q_\varepsilon)}.$$
--
--   Thus even the square root of the Chernoff distance need not satisfy the triangle inequality. Positivity of $\varepsilon$ keeps every term finite.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 17, §4.3, triangle-inequality failure

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

/-- arXiv:0708.4282v1, PDF p.17: §4.3, triangle-inequality failure. -/
theorem triangleFailure  : ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1/2 ∧
    ∀ eps : ℝ, 0 < eps → eps < delta →
    let p : Fin 2 → ℝ := ![eps,1-eps]
    let q : Fin 2 → ℝ := ![1-eps,eps]
    let u : Fin 2 → ℝ := ![1/2,1/2]
    classicalDistance p q ≠ ⊤ ∧ classicalDistance p u ≠ ⊤ ∧
    classicalDistance u q ≠ ⊤ ∧
    Real.sqrt (classicalDistance p u).toReal + Real.sqrt (classicalDistance u q).toReal <
      Real.sqrt (classicalDistance p q).toReal := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
