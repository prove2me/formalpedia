-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P31_remark4
-- name    : QAlgorithms.Papers.Independent.Bridge50.P31.remark4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:59:30.462864+00:00
-- url     : https://prove2.me/theorems/f1fbcd11-9b1b-451e-b3e9-b9caf280b11a
-- title:
--   Remark 4: preservation of the Bures metric is insufficient
-- statement:
--   Let $A\subseteq B(H)$ and $B\subseteq B(K)$ be concrete finite-dimensional unital complex $C^*$-algebras on nonzero representation spaces. Maps are complex linear, $\operatorname{Tr}$ is the unnormalized representation trace, and $T^*$ is the Hilbert–Schmidt adjoint for $\langle a,b\rangle=\operatorname{Tr}(a^*b)$. A density operator is positive with trace one. All inverses of singular positive operators below are support inverses.
--
--   Let $\rho$ be a faithful density and $y=y^*\in A$ satisfy $\rho y\ne y\rho$ and $\operatorname{Tr}(\rho y)=0$. Let $C=C^*(y)$ and $T:A\to C$ be the computed trace-preserving conditional expectation. There is $c>0$ such that, writing $y_c=cy$, $z=\rho y_c+y_c\rho$ and $\sigma=\rho+z$, the state $\sigma$ is faithful. Then
--   $$
--   (L_\rho+R_\rho)^{-1}(\sigma-\rho)=y_c=
--   (L_{T(\rho)}+R_{T(\rho)})^{-1}(T(\sigma)-T(\rho)).
--   $$
--   For $f(t)=(1+t)/2$, the Bures metric is $\lambda_\rho^f(z,z)=2\operatorname{Tr}z(L_\rho+R_\rho)^{-1}(z)$; both this metric value and $\chi^2_{1/f}(\sigma,\rho)$ are preserved. Nevertheless
--   $$
--   [\sigma,\rho]=[y_c,\rho^2]\ne0,\qquad T\text{ is not reversible for }\{\rho,\sigma\}.
--   $$
--   Here $[a,b]=ab-ba$. The positive scaling is constructed, and the factor two in the metric is retained.
-- source:
--   Reversibility conditions for quantum operations, arXiv:1107.0453v2, PDF p. 25, Remark 4: preservation of the Bures metric is insufficient

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P31

open Filter MeasureTheory Set

open scoped Matrix ComplexOrder ComplexConjugate BigOperators Topology

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE)

open QAlgorithms.Papers.Independent.Dependency50.P21
  (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports matrixCommutant)

open QAlgorithms.Papers.Independent.Support50.P12
  (Alg AlgebraDensity AlgebraExtension PositiveOnConcreteAlgebra AlgebraTracePreserving
   AlgebraKPositive AlgebraCompletelyPositive supp spec cpow quasi hull modularSpec)

open QAlgorithms.Papers.Independent.Information100.P50 (OperatorMonotone)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- PDF p.25, Remark 4: a POSITIVE scaling supplies a faithful perturbation.
For [a,b]=ab-ba the printed sign is corrected to [sigma,rho]=[y,rho^2].
The resolvent, factor-two Bures metric, chi-squared equality and failure of
reversibility are all retained. These source corrections require moderation. -/
theorem remark4 [Nonempty I] (A : Alg I) (rho y : Mat I)
    (hrho : AlgebraDensity A rho) (hfaith : rho.PosDef)
    (hy : y ∈ A) (hystar : y.IsHermitian)
    (hnoncomm : rho * y ≠ y * rho) (htrace : (rho * y).trace = 0) :
    let C : Alg I := StarAlgebra.adjoin ℂ ({y} : Set (Mat I))
    let T := traceConditionalExpectation A C
    let f : ℝ → ℝ := fun t => (1 + t) / 2
    ∃ c : ℝ, 0 < c ∧
      let ys := (c : ℂ) • y
      let z := rho * ys + ys * rho
      let sigma := rho + z
      Tangent A z ∧ AlgebraDensity A sigma ∧ sigma.PosDef ∧
      T sigma = T rho + T rho * ys + ys * T rho ∧
      resolvent rho rho 1 (sigma - rho) = ys ∧
      resolvent (T rho) (T rho) 1 (T sigma - T rho) = ys ∧
      metric f rho z z = 2 * tr (z * resolvent rho rho 1 z) ∧
      metric f rho z z = metric f (T rho) (T z) (T z) ∧
      chiSquared f sigma rho = chiSquared f (T sigma) (T rho) ∧
      sigma * rho - rho * sigma = ys * (rho * rho) - (rho * rho) * ys ∧
      sigma * rho ≠ rho * sigma ∧ ¬ FamilyReversible A C T {rho, sigma} := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P31

end
