-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_golden_thompson_family
-- name    : QAlgorithms.Papers.Independent.Next46.P23.golden_thompson_family
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:49:21.495488+00:00
-- url     : https://prove2.me/theorems/7b58ed48-e8c5-4499-810b-ef377d2fc68d
-- title:
--   Corollary 2.3
-- statement:
--   For self-adjoint $A,B$ on a nonzero finite-dimensional complex Hilbert space, define $F(p)=\|e^{B/p}e^{A/p}\|_p^p$ for real $p\ge1$. Then $$F(p)=\operatorname{tr}[(e^{A/p}e^{2B/p}e^{A/p})^{p/2}],\qquad\lim_{p\to\infty}F(p)=\operatorname{tr}(e^{A+B}).$$ The function $F$ is nonincreasing. At $p=2$ its value is $\operatorname{tr}(e^Ae^B)$, giving Golden–Thompson, $\operatorname{tr}(e^Ae^B)\ge\operatorname{tr}(e^{A+B})$.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 38, Corollary 2.3

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

/-- Corollary2.3 including its limit and Golden--Thompson consequence, source PDF p.38. -/
theorem golden_thompson_family [Nonempty I] (A B : Mat I) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    let F : ℝ → ℝ := fun p =>
      (schattenNorm (ENNReal.ofReal p)
        (NormedSpace.exp ((p⁻¹ : ℂ) • B) * NormedSpace.exp ((p⁻¹ : ℂ) • A))) ^ p
    AntitoneOn F (Set.Ici 1) ∧
    (∀ p : ℝ, 1 ≤ p → F p =
      (supportPower (NormedSpace.exp ((p⁻¹ : ℂ) • A) *
        NormedSpace.exp (((2 / p : ℝ) : ℂ) • B) *
        NormedSpace.exp ((p⁻¹ : ℂ) • A)) (p/2)).trace.re) ∧
    Tendsto F atTop (nhds ((NormedSpace.exp (A + B)).trace.re)) ∧
    (NormedSpace.exp (A + B)).trace.re ≤ (NormedSpace.exp A * NormedSpace.exp B).trace.re ∧
    (NormedSpace.exp A * NormedSpace.exp B).trace.re =
      schattenNorm 2 (NormedSpace.exp ((1/2 : ℂ) • B) *
        NormedSpace.exp ((1/2 : ℂ) • A)) ^ (2 : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
