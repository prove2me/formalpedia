-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_renyi_joint_concavity
-- name    : QAlgorithms.Papers.Independent.Next46.P23.renyi_joint_concavity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:58:18.925154+00:00
-- url     : https://prove2.me/theorems/6e170013-52ca-4e51-8a1b-b53541d3fb1a
-- title:
--   Theorem 2.14
-- statement:
--   For four normalized states $\rho,\rho^\prime,\nu,\nu^\prime$ on a nonzero finite-dimensional complex Hilbert space and $\alpha,u\in[0,1]$, $$S_\alpha(u\rho+(1-u)\rho^\prime\mid u\nu+(1-u)\nu^\prime)\ge uS_\alpha(\rho\mid\nu)+(1-u)S_\alpha(\rho^\prime\mid\nu^\prime).$$ Values are extended real, with support-restricted powers at both endpoints. This is joint concavity without a faithfulness restriction.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 46, Theorem 2.14

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

/-- Theorem2.14, joint concavity including singular inputs and endpoints, source PDF pp.46--47. -/
theorem renyi_joint_concavity [Nonempty I] (rho rhoAlt nu nuAlt : Mat I)
    (hrho : QAlgorithms.IsDensityMatrix rho) (hrhoAlt : QAlgorithms.IsDensityMatrix rhoAlt)
    (hnu : QAlgorithms.IsDensityMatrix nu) (hnuAlt : QAlgorithms.IsDensityMatrix nuAlt)
    (a u : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (u : EReal) * renyi rho nu a + ((1-u : ℝ) : EReal) * renyi rhoAlt nuAlt a ≤
      renyi ((u : ℂ) • rho + ((1-u : ℝ) : ℂ) • rhoAlt)
        ((u : ℂ) • nu + ((1-u : ℝ) : ℂ) • nuAlt) a := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
