-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_kosaki_variational
-- name    : QAlgorithms.Papers.Independent.Next46.P23.kosaki_variational
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:56:48.696991+00:00
-- url     : https://prove2.me/theorems/04de2760-96f8-4168-b93a-d6e4b3c00c1f
-- title:
--   Theorem 2.12
-- statement:
--   For normalized states $\rho,\nu$ on a nonzero finite-dimensional complex Hilbert space and $0<\alpha<1$, $$S_\alpha(\rho\mid\nu)=\inf_{A\in C((0,\infty),B(K))}\log\left[\frac{\sin\pi\alpha}{\pi}\int_0^\infty t^{\alpha-1}\left(\frac{\rho(A(t)A(t)^*)}{t}+\nu((I-A(t))^*(I-A(t)))\right)dt\right].$$ The integral is nonnegative and extended, and the logarithm retains $-\infty$ at zero. The infimum is attained by the continuous function $A(t)=t\int_0^\infty e^{-s\rho}\nu e^{-st\nu}ds$; this function is the unique minimizer if either state is faithful. No faithfulness assumption is imposed on the variational formula.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 46, Theorem 2.12

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

/-- Theorem2.12 with constructed minimizer and conditional uniqueness, source PDF p.46. -/
theorem kosaki_variational [Nonempty I] (rho nu : Mat I) (hrho : QAlgorithms.IsDensityMatrix rho)
    (hnu : QAlgorithms.IsDensityMatrix nu) (a : ℝ) (ha : 0 < a) (haone : a < 1) :
    renyi rho nu a = sInf {v | ∃ A : ℝ → Mat I,
      ContinuousOn A (Set.Ioi 0) ∧ v = kosakiCost rho nu a A} ∧
    ContinuousOn (kosakiMinimizer rho nu) (Set.Ioi 0) ∧
    kosakiCost rho nu a (kosakiMinimizer rho nu) = renyi rho nu a ∧
    (rho.PosDef ∨ nu.PosDef → ∀ A : ℝ → Mat I, ContinuousOn A (Set.Ioi 0) →
      (kosakiCost rho nu a A = renyi rho nu a ↔
        Set.EqOn A (kosakiMinimizer rho nu) (Set.Ioi 0))) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
