-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_araki_lieb_thirring
-- name    : QAlgorithms.Papers.Independent.Next46.P23.araki_lieb_thirring
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:47:55.263992+00:00
-- url     : https://prove2.me/theorems/cf61ab33-690f-496e-9d81-7b8727ad7f11
-- title:
--   Theorem 2.2
-- statement:
--   Let $A,B\ge0$ act on a nonzero finite-dimensional complex Hilbert space. For $p>0$ and $r\ge1$, $$\operatorname{tr}[(A^{1/2}BA^{1/2})^{rp}]\le\operatorname{tr}[(A^{r/2}B^rA^{r/2})^p].$$ Powers use the positive spectral calculus, and singular operators are permitted. This is the Araki–Lieb–Thirring inequality.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 37, Theorem 2.2

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

/-- Theorem2.2, Araki--Lieb--Thirring, source PDF p.37; p>0 and r>=1. -/
theorem araki_lieb_thirring [Nonempty I] (A B : Mat I) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (p r : ℝ) (hp : 0 < p) (hr : 1 ≤ r) :
    (supportPower (supportPower A (1/2) * B * supportPower A (1/2)) (r * p)).trace.re ≤
      (supportPower (supportPower A (r/2) * supportPower B r * supportPower A (r/2)) p).trace.re := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
