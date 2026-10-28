-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_entropy_and_partition_convexity
-- name    : QAlgorithms.Papers.Independent.Next46.P23.entropy_and_partition_convexity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T18:54:18.377949+00:00
-- url     : https://prove2.me/theorems/3881b730-bffc-42cf-b383-cf9ba8439f3c
-- title:
--   Corollary 2.9
-- statement:
--   On normalized positive matrices on a nonzero finite-dimensional complex Hilbert space, entropy in nats is concave; on self-adjoint matrices the log-partition function is convex. Explicitly, for $0\le u\le1$, $$S(u\rho+(1-u)\nu)\ge uS(\rho)+(1-u)S(\nu),\quad \log\operatorname{tr}e^{uA+(1-u)B}\le u\log\operatorname{tr}e^A+(1-u)\log\operatorname{tr}e^B.$$ These are the two convexity consequences of entropy duality.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 44, Corollary 2.9

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

/-- Corollary2.9, source PDF p.44: entropy concavity and log-partition convexity. -/
theorem entropy_and_partition_convexity [Nonempty I] :
    (∀ rho nu : Mat I, QAlgorithms.IsDensityMatrix rho → QAlgorithms.IsDensityMatrix nu →
      ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      u * entropy rho + (1-u) * entropy nu ≤ entropy ((u : ℂ) • rho + ((1-u : ℝ) : ℂ) • nu)) ∧
    (∀ A B : Mat I, A.IsHermitian → B.IsHermitian →
      ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      Real.log ((NormedSpace.exp ((u : ℂ) • A + ((1-u : ℝ) : ℂ) • B)).trace.re) ≤
        u * Real.log ((NormedSpace.exp A).trace.re) +
          (1-u) * Real.log ((NormedSpace.exp B).trace.re)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
