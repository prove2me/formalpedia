-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_quantum_evans_searles
-- name    : QAlgorithms.Papers.Independent.Next46.P23.quantum_evans_searles
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T18:45:40.169703+00:00
-- url     : https://prove2.me/theorems/b69a5498-c422-43ce-bbd1-e134470e7a8d
-- title:
--   Paper seed: finite-time quantum Evans–Searles symmetry (Proposition 3.3(7))
-- statement:
--   Let $H=H^*$ act on a nonzero finite-dimensional complex Hilbert space and let $\omega>0$ be a normalized state. Write $\omega_t=e^{-itH}\omega e^{itH}$ and $e_{p,t}$ for the entropic pressure defined by the source, with its exponential definition at $p=\infty$. If an anti-linear involutive star-automorphism reverses the dynamics and preserves the state, then, for every $p\in[1,\infty]$ and real $t,\alpha$, $$e_{p,t}(\alpha)=e_{p,t}(1-\alpha).$$ This is the seed result, intentionally also included in Proposition 3.3.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 74, Paper seed: finite-time quantum Evans–Searles symmetry (Proposition 3.3(7))

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

/-- Paper seed: Proposition3.3(7), finite-time quantum ES, source PDF pp.71,74.
The full p=infinity endpoint and every real alpha,t are included; TRI is conditional. -/
theorem quantum_evans_searles [Nonempty I] (H omega : Mat I) (hH : H.IsHermitian)
    (homega : QAlgorithms.IsDensityMatrix omega) (hfaithful : omega.PosDef)
    (htri : TRI H omega) (p : ℝ≥0∞) (hp : 1 ≤ p) (t a : ℝ) :
    pressure H omega p t a = pressure H omega p t (1-a) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
