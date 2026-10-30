-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_expected_cost_parameter_law
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.expected_cost_parameter_law
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:46:57.728474+00:00
-- url     : https://prove2.me/theorems/c2e02c4e-7513-4d70-9eb0-6d165a3ba1ee
-- title:
--   Appendix D: expected cost depends only on parameter-conditioned outcome laws
-- statement:
--   For a physical $n$-copy channel experiment with probability prior $p$, finite measurable parameter vector $s$, and arbitrary measurable outcome space, let $K(\rho,dt)$ be the normalized Born kernel satisfying $K(\rho,B)=\operatorname{tr}(M(B)\mathcal E(\rho^{\otimes n}))$ on the prior support. Let $\nu_M$ be the pushforward of $p(d\rho)K(\rho,dt)$ under $(\rho,t)\mapsto(t,s(\rho))$. Then
--   $$\int p(d\rho)\int C(t,s(\rho))K(\rho,dt)=\int C(t,S)\,\nu_M(dt,dS).$$
--   This holds for nonnegative measurable costs, allowing infinity, and for real measurable costs integrable under the joint law. Equality of all positive-probability parameter-box conditional laws implies equality of $\nu_M$. Under Theorem 11 or 13 there is an $\mathcal A^{\otimes n}$-valued POVM with the same joint law, preserving every such cost and any attained optimum.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 39, Appendix D: expected cost depends only on parameter-conditioned outcome laws

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P37

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Next46.P29 (phaseAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixBorel

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- PDF pp.39-40, Appendix D: the general expected-cost change of variables,
for nonnegative possibly infinite costs and integrable real costs, followed
by the local-algebra restriction under Theorem 11/13. The n-copy channel
embedding suppressed in printed (D2) is restored in BornKernel. -/
theorem expected_cost_parameter_law [Nonempty I] {O : Type*} [MeasurableSpace O]
    (n : ℕ) (hn : 0 < n) {l : ℕ} (p : EstimationPrior I l)
    (E : Mat (Fin n → I) → Mat (Fin n → I)) (hE : IsChannel E)
    (M : Measurements.OperatorPOVM (Fin n → I) O)
    (K : ProbabilityTheory.Kernel (Mat I) O) [ProbabilityTheory.IsMarkovKernel K]
    (hK : BornKernel p E M K) :
    (∀ C : O × (Fin l → ℝ) → ENNReal, Measurable C →
      (∫⁻ rho, ∫⁻ t, C (t, p.parameter rho) ∂K rho ∂p.law) =
        ∫⁻ x, C x ∂parameterJoint p K) ∧
    (∀ C : O × (Fin l → ℝ) → ℝ, Measurable C →
      Integrable (fun x => C (x.2, p.parameter x.1)) (p.law.compProd K) →
      (∫ rho, ∫ t, C (t, p.parameter rho) ∂K rho ∂p.law) =
        ∫ x, C x ∂parameterJoint p K) ∧
    (∀ (N : Measurements.OperatorPOVM (Fin n → I) O)
        (L : ProbabilityTheory.Kernel (Mat I) O), ProbabilityTheory.IsMarkovKernel L →
      BornKernel p E N L → EquallyInformative p (E ∘ piKron n) M.operator N.operator →
        parameterJoint p K = parameterJoint p L) ∧
    (∀ A : StarSubalgebra ℂ (Mat I), EstimationAssumptions (A : Set (Mat I)) n p E →
      ∃ N : Measurements.OperatorPOVM (Fin n → I) O,
        InAlgebra N.operator (tensorAlg n (A : Set (Mat I))) ∧
        ∃ L : ProbabilityTheory.Kernel (Mat I) O, ProbabilityTheory.IsMarkovKernel L ∧
          BornKernel p E N L ∧ parameterJoint p K = parameterJoint p L) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
