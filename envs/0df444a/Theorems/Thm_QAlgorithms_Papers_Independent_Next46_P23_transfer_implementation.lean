-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_transfer_implementation
-- name    : QAlgorithms.Papers.Independent.Next46.P23.transfer_implementation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T19:51:36.79787+00:00
-- url     : https://prove2.me/theorems/b2004f64-b744-4e4e-bf59-12850599030d
-- title:
--   Proposition 3.4
-- statement:
--   Let $H=H^*$ and $\omega>0$ be normalized on a nonzero finite-dimensional complex Hilbert space. For $p\in[1,\infty]$, $$U_p(t)\xi=e^{-itH}\xi\omega^{-1/2+1/p}e^{itH}\omega^{1/2-1/p}.$$ These maps form a group of linear isometries of the intrinsically defined Araki–Masuda space, preserve its positive cone, and satisfy $U_p(-t)L(A)U_p(t)=L(\tau^t(A))$. They are uniquely characterized by these three properties. This includes both endpoint exponents.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 76, Proposition 3.4

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

/-- Proposition3.4, all four clauses including uniqueness of the implementing group;
source PDF pp.76--77. -/
theorem transfer_implementation [Nonempty I] (H omega : Mat I) (hH : H.IsHermitian)
    (homega : QAlgorithms.IsDensityMatrix omega) (hfaithful : omega.PosDef)
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    LpImplements H omega p (transfer H omega p) ∧
    ∀ W : ℝ → Mat I → Mat I, LpImplements H omega p W →
      ∀ t xi, W t xi = transfer H omega p t xi := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
