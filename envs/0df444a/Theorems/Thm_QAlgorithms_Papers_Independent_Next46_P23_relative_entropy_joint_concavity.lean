-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_relative_entropy_joint_concavity
-- name    : QAlgorithms.Papers.Independent.Next46.P23.relative_entropy_joint_concavity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T19:38:59.644707+00:00
-- url     : https://prove2.me/theorems/3393fcfa-8d89-4e95-b84a-459b49b69e7d
-- title:
--   Theorem 2.18
-- statement:
--   For four normalized states on a nonzero finite-dimensional complex Hilbert space and $u\in[0,1]$, signed relative entropy satisfies $$S(u\rho+(1-u)\rho^\prime\mid u\nu+(1-u)\nu^\prime)\ge uS(\rho\mid\nu)+(1-u)S(\rho^\prime\mid\nu^\prime).$$ Entropies retain $-\infty$ when support inclusion fails. This is joint concavity with the source’s sign convention.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 49, Theorem 2.18

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

/-- Theorem2.18, joint concavity of signed relative entropy, source PDF pp.49--50. -/
theorem relative_entropy_joint_concavity [Nonempty I] (rho rhoAlt nu nuAlt : Mat I)
    (hrho : QAlgorithms.IsDensityMatrix rho) (hrhoAlt : QAlgorithms.IsDensityMatrix rhoAlt)
    (hnu : QAlgorithms.IsDensityMatrix nu) (hnuAlt : QAlgorithms.IsDensityMatrix nuAlt)
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (u : EReal) * signedRelativeEntropy rho nu + ((1-u : ℝ) : EReal) * signedRelativeEntropy rhoAlt nuAlt ≤
      signedRelativeEntropy ((u : ℂ) • rho + ((1-u : ℝ) : ℂ) • rhoAlt)
        ((u : ℂ) • nu + ((1-u : ℝ) : ℂ) • nuAlt) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
