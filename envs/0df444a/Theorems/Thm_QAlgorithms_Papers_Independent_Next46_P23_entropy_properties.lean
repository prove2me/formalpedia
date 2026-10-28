-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_entropy_properties
-- name    : QAlgorithms.Papers.Independent.Next46.P23.entropy_properties
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T18:55:24.61923+00:00
-- url     : https://prove2.me/theorems/90a37e2d-029d-47ea-9e33-98f4ebddff40
-- title:
--   Theorem 2.10
-- statement:
--   For normalized positive matrices on a nonzero finite-dimensional complex Hilbert space $K$, entropy in nats is continuous and $$0\le S(\rho)\le\log\dim K.$$ Its lower equality holds exactly for pure states, and its upper equality exactly for $I/\dim K$. Entropy is invariant under unitary conjugation. For $\rho_A=e^A/\operatorname{tr}(e^A)$, $S(\rho_A)=\log\operatorname{tr}(e^A)-\rho_A(A)$. For every bipartite state, $S(\rho)\le S(\rho_1)+S(\rho_2)$, with equality exactly for $\rho=\rho_1\otimes\rho_2$; the marginals use unnormalized partial traces. All five clauses and equality cases are retained.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 44, Theorem 2.10

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Next46.P23

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15 (propagator legendre rightSlope leftSlope FiniteExperiment exponentialMoment)

open QAlgorithms.Papers.Independent.Dependency50.P05 (uniformDensity)

open QAlgorithms.Papers.Independent.Dependency50.P28 (Schwarz)

open QAlgorithms.Papers.Independent.Frontier30.P28 (inverseExponent)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms (traceRight)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Theorem2.10, all five clauses with equality cases, source PDF p.44. -/
theorem entropy_properties [Nonempty I] :
    ContinuousOn (entropy : Mat I → ℝ) {rho | QAlgorithms.IsDensityMatrix rho} ∧
    (∀ rho : Mat I, QAlgorithms.IsDensityMatrix rho →
      0 ≤ entropy rho ∧ entropy rho ≤ Real.log (Fintype.card I) ∧
      (entropy rho = 0 ↔ ∃ psi : EuclideanSpace ℂ I,
        QAlgorithms.IsState psi ∧ rho = QAlgorithms.pureDensity psi) ∧
      (entropy rho = Real.log (Fintype.card I) ↔ rho = uniformDensity I)) ∧
    (∀ rho : Mat I, QAlgorithms.IsDensityMatrix rho → ∀ U : Matrix.unitaryGroup I ℂ,
      entropy ((U : Mat I) * rho * (U : Mat I)ᴴ) = entropy rho) ∧
    (∀ A : Mat I, A.IsHermitian →
      entropy (QAlgorithms.gibbsState A) = Real.log ((NormedSpace.exp A).trace.re) - ev (QAlgorithms.gibbsState A) A) ∧
    (∀ (K L : Type) [Fintype K] [DecidableEq K] [Nonempty K]
      [Fintype L] [DecidableEq L] [Nonempty L],
      ∀ rho : Mat (K × L), QAlgorithms.IsDensityMatrix rho →
      entropy rho ≤ entropy (traceRight rho) + entropy (QAlgorithms.traceLeft rho) ∧
      (entropy rho = entropy (traceRight rho) + entropy (QAlgorithms.traceLeft rho) ↔
        rho = Matrix.kronecker (traceRight rho) (QAlgorithms.traceLeft rho))) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
