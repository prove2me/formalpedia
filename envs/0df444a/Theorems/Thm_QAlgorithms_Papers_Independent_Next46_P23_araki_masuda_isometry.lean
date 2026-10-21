-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_araki_masuda_isometry
-- name    : QAlgorithms.Papers.Independent.Next46.P23.araki_masuda_isometry
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:46:21.041587+00:00
-- url     : https://prove2.me/theorems/4f64a068-19b2-4f33-b692-7ee610389626
-- title:
--   Theorem 2.25
-- statement:
--   Let $\omega$ be a faithful normalized state on a nonzero finite-dimensional complex Hilbert space. Define the Araki–Masuda norm intrinsically by maximization of relative-modular Hilbert–Schmidt norms for $p\ge2$ and by duality for $1\le p<2$. For every $p\in[1,\infty]$, $$\|\xi\|_{\omega,p}=\|\xi\omega^{1/p-1/2}\|_p.$$ Consequently $\xi\mapsto\xi\omega^{1/2-1/p}$ is a surjective isometry from Schatten $L^p$ to the reference-dependent space. Multiplication is on the right, and $1/\infty=0$.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 66, Theorem 2.25

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

/-- Theorem2.25, the weighted right-multiplication norm identity and surjective isometry;
source PDF p.66. amNorm has the source's independent maximization/duality definition. -/
theorem araki_masuda_isometry [Nonempty I] (omega : Mat I) (homega : QAlgorithms.IsDensityMatrix omega)
    (hfaithful : omega.PosDef) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    (∀ xi : Mat I, amNorm omega p xi =
      schattenNorm p (xi * supportPower omega (inverseExponent p-1/2))) ∧
    (∀ xi : Mat I, amNorm omega p (xi * supportPower omega (1/2-inverseExponent p)) = schattenNorm p xi) ∧
    (∀ eta : Mat I, ∃ xi : Mat I, xi * supportPower omega (1/2-inverseExponent p) = eta) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
