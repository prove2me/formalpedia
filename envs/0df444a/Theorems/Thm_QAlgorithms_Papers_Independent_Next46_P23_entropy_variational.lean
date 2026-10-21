-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_entropy_variational
-- name    : QAlgorithms.Papers.Independent.Next46.P23.entropy_variational
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:53:17.329897+00:00
-- url     : https://prove2.me/theorems/82e5696d-3d07-4967-9d27-79a3bca4fe40
-- title:
--   Theorem 2.8
-- statement:
--   For a normalized positive matrix $\rho$, write $P=s(\rho)$ and $S(\rho)=-\operatorname{tr}(\rho\log\rho)$, in nats. On a nonzero finite-dimensional space, $$S(\rho)=\min_{A=A^*}\{\log\operatorname{tr}(Pe^A)-\rho(A)\},\qquad \log\operatorname{tr}(e^A)=\max_\rho\{\rho(A)+S(\rho)\}.$$ The minimum is attained; equality in the first formula holds exactly when $A$ preserves the support and $PAP=\log\rho+cP$ for a real $c$. The second maximizer is uniquely $e^A/\operatorname{tr}(e^A)$. These are attained entropy duality formulas.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 43, Theorem 2.8

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

/-- Theorem2.8 and its equality/attainment Remark, source PDF pp.43--44. -/
theorem entropy_variational [Nonempty I] :
    (∀ rho : Mat I, QAlgorithms.IsDensityMatrix rho →
      (∀ A : Mat I, A.IsHermitian → entropy rho ≤
        Real.log (ev (support rho) (NormedSpace.exp A)) - ev rho A) ∧
      (∃ A : Mat I, A.IsHermitian ∧ entropy rho =
        Real.log (ev (support rho) (NormedSpace.exp A)) - ev rho A) ∧
      (∀ A : Mat I, A.IsHermitian →
        (entropy rho = Real.log (ev (support rho) (NormedSpace.exp A)) - ev rho A ↔
          ∃ c : ℝ, A * support rho = support rho * A ∧
            support rho * A * support rho = logMat rho + (c : ℂ) • support rho))) ∧
    (∀ A : Mat I, A.IsHermitian →
      QAlgorithms.IsDensityMatrix (QAlgorithms.gibbsState A) ∧
      (∀ rho : Mat I, QAlgorithms.IsDensityMatrix rho →
        ev rho A + entropy rho ≤ Real.log ((NormedSpace.exp A).trace.re) ∧
        (ev rho A + entropy rho = Real.log ((NormedSpace.exp A).trace.re) ↔ rho = QAlgorithms.gibbsState A))) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
