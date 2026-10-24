-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P24_exponentialTests
-- name    : QAlgorithms.Papers.Independent.Renew46.P24.exponentialTests
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:40:01.484614+00:00
-- url     : https://prove2.me/theorems/ed10529c-628f-421f-ac59-36682a6b8f3e
-- title:
--   Remark 2.2: exponential sums and ordered exponential products
-- statement:
--   In the uniformly bounded self-adjoint setting of Proposition 2.1, let nonzero projections $P^N$ concentrate at $x$. Write $\operatorname{tr}(A\mid P^N)=\operatorname{Tr}(P^NA)/\operatorname{Tr}P^N$. Any two absolutely weighted-summable noncommutative analytic series agreeing as scalar functions on the real multidisc $|y_k|<r_k$ have the same limiting expectation.
--
--   For every finite $R\subset K$, complex parameters $\lambda_k$, and every enumeration $k_1,\ldots,k_m$ of $R$ without repetition,
--
--   $$\lim_{N\to\infty}\operatorname{tr}\!\left(\exp\!\left[\sum_{k\in R}\lambda_k(X_k^N-x_kI)\right]\mid P^N\right)=\lim_{N\to\infty}\operatorname{tr}\!\left(\prod_{j=1}^{m}\exp[\lambda_{k_j}(X_{k_j}^N-x_{k_j}I)]\mid P^N\right)=1.$$
--
--   The product is taken in the displayed order, and the conclusion holds for every order, including the empty product. This describes limiting equivalence of different operator orderings.
-- source:
--   Quantum Macrostates, Equivalence of Ensembles and an H-Theorem, arXiv:math-ph/0601027v2, PDF p. 5, Remark 2.2: exponential sums and ordered exponential products

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P24

open Filter

open scoped Topology ComplexOrder Matrix.Norms.L2Operator

-- Exact primitives verified against the pinned accepted-library SHA256 catalogue.

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

open QAlgorithms.Papers.Independent.Dependency50.P21 (spectralFunction relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Remark 2.2, PDF p.5: classically equivalent tests have the same limiting
traceExpectation; centered exponential sums and every ordered exponential product tend to one. -/
theorem exponentialTests {K : Type*} (S : MacroscopicSystem K)
    (hS : IsMacroscopic S) (P : OperatorSequence S) (x : K → ℝ)
    (hP : projectionConcentrates S P x) :
    (∀ G H : AnalyticTestSeries S,
      (∀ y : K → ℝ, (∀ k, |y k| < S.radius k) →
        scalarEvaluation G y = scalarEvaluation H y) →
      ∃ z : ℂ,
        Tendsto (fun n => traceExpectation (projectionDensity P n) (operatorEvaluation G n))
          atTop (𝓝 z) ∧
        Tendsto (fun n => traceExpectation (projectionDensity P n) (operatorEvaluation H n))
          atTop (𝓝 z)) ∧
    ∀ (R : Finset K) (order : List K), order.Nodup →
      (∀ k, k ∈ order ↔ k ∈ R) → ∀ lambda : K → ℂ,
      Tendsto (fun n => traceExpectation (projectionDensity P n)
        (NormedSpace.exp (∑ k ∈ R,
          lambda k • (S.observable n k - (x k : ℂ) • 1)))) atTop (𝓝 (1 : ℂ)) ∧
      Tendsto (fun n => traceExpectation (projectionDensity P n)
        ((order.map (fun k => NormedSpace.exp
          (lambda k • (S.observable n k - (x k : ℂ) • 1)))).prod))
        atTop (𝓝 (1 : ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P24

end
