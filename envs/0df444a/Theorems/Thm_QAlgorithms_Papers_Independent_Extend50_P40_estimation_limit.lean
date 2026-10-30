-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_estimation_limit
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.estimation_limit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:13:26.895351+00:00
-- url     : https://prove2.me/theorems/2324838b-658b-41e2-9645-88ca2081af9d
-- title:
--   §II.E Eq.(45): qubit cloning/estimation equivalence
-- statement:
--   For $N\ge1$ identical pure qubits there exists a finite POVM with positive effects summing to the Bose projector $S_N$ and normalized pure guesses. Its mean prepared estimate is $\eta_*|\psi\rangle\langle\psi|+(1-\eta_*)I/2$ for every input, where
--
--   $$
--   \eta_*(N)=\frac{N}{N+2}=\lim_{M\to\infty}\eta(N,M).
--   $$
--
--   Any estimator with constant fidelity has fidelity at most (N+1)/(N+2). The missing tensor power in the printed probability is restored. This is an asymptotic comparison of finite cloners, not a literal infinite tensor-output channel.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 13, §II.E Eq.(45): qubit cloning/estimation equivalence

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P40

open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate BigOperators Topology

open MeasureTheory Filter

open scoped Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P12 (sigma)

open QAlgorithms.Papers.Independent.Dependency50.P48 (pureFidelity)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support21.P16
  (CloneMap IsBoseInputChannel coherentTensor tensorWithIdentity canonicalCloner
   HasBoseOutput HasBlackCowCoefficient canonicalCoefficient oneMixed)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector siteObservable)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

/-- II.E, PDF pp.13–14 Eqs.(43)–(45): the optimal finite estimator has the same
shrinking factor as the limit of optimal finite-output cloners. -/
theorem estimation_limit (N : ℕ) (hN : 1 ≤ N) :
    (∃ E : Estimator N, ∀ psi : EuclideanSpace ℂ (Fin 2), ‖psi‖ = 1 →
      estimationOutput E psi = depol (estimationShrink N) (pureDensity psi)) ∧
    (∀ (E : Estimator N) (f : ℝ),
      (∀ psi : EuclideanSpace ℂ (Fin 2), ‖psi‖ = 1 → pureFidelity psi (estimationOutput E psi) = f) →
        f ≤ ((N : ℝ) + 1) / (N + 2)) ∧
    Tendsto (fun M : ℕ => canonicalCoefficient 2 N M) atTop (nhds (estimationShrink N)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
