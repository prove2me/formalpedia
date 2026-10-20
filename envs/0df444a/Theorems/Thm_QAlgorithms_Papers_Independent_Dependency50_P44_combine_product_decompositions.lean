-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P44_combine_product_decompositions
-- name    : QAlgorithms.Papers.Independent.Dependency50.P44.combine_product_decompositions
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:27:43.656773+00:00
-- url     : https://prove2.me/theorems/4d2975a6-d64d-4d23-a93d-60221e47ab1c
-- title:
--   Combining two approximate product decompositions
-- statement:
--   Let $A,B,C$ be finite-dimensional nonzero complex Hilbert spaces. Let $\rho^{ABC},\sigma^A,\omega^{BC},\tau^{AB},\eta^C$ be normalized density operators, and let $\varepsilon_1,\varepsilon_2\in\mathbb R$ satisfy
--
--   $$\|\rho-\sigma\otimes\omega\|_1\le\varepsilon_1,\qquad
--   \|\rho-\tau\otimes\eta\|_1\le\varepsilon_2.$$
--
--   For the computed marginal $\tau^B=\operatorname{Tr}_A\tau^{AB}$,
--
--   $$\|\rho^{ABC}-\sigma^A\otimes\tau^B\otimes\eta^C\|_1\le2\varepsilon_1+\varepsilon_2.$$
--
--   The norm is the unhalved trace norm. The assumptions already force the two error bounds to be nonnegative. This lemma combines two approximate product decompositions into a common product structure.
-- source:
--   A father protocol for quantum broadcast channels, arXiv:quant-ph/0612155v4, PDF p. 4, Lemma 1

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P44

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

open Filter Topology

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P44

open QAlgorithms.Papers.Independent.Information100.P58 (Operator)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst)

/-- PDF p.4, Lemma 1: combining two normalized approximate product decompositions.
The B state in the conclusion is the computed marginal of tau, not an independent parameter. -/
theorem combine_product_decompositions {A B C : Type}
    [Fintype A] [Fintype B] [Fintype C] [Nonempty A] [Nonempty B] [Nonempty C]
    (rho : Operator (A × (B × C))) (sigma : Operator A) (omega : Operator (B × C))
    (tau : Operator (A × B)) (eta : Operator C)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (homega : IsDensityMatrix omega) (htau : IsDensityMatrix tau) (heta : IsDensityMatrix eta)
    (eps1 eps2 : ℝ)
    (h1 : traceNorm (rho - Matrix.kronecker sigma omega) ≤ eps1)
    (h2 : traceNorm (rho - (show Operator (A × (B × C)) from
      fun x y => Matrix.kronecker tau eta
        ((x.1, x.2.1), x.2.2) ((y.1, y.2.1), y.2.2))) ≤ eps2) :
    traceNorm (rho - Matrix.kronecker sigma (Matrix.kronecker (traceLeft tau) eta)) ≤
      2 * eps1 + eps2 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P44

end
