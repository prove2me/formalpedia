-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_entropy_production_initial
-- name    : QAlgorithms.Papers.Independent.Next46.P23.entropy_production_initial
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T19:49:02.343196+00:00
-- url     : https://prove2.me/theorems/aedce965-e231-4c90-ab7e-b744371243b7
-- title:
--   Proposition 3.2
-- statement:
--   For a nonzero finite-dimensional quantum dynamical system with self-adjoint $H$ and faithful normalized $\omega$, define $\sigma=-i[H,\log\omega]$. Then $$\omega(\sigma)=0.$$ For every reversal $\Theta$ preserving this system, $\Theta(\sigma)=-\sigma$. The initial mean vanishes without TRI.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 72, Proposition 3.2

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

/-- Proposition3.2, vanishing initial mean and conditional oddness; source PDF p.72. -/
theorem entropy_production_initial [Nonempty I] (H omega : Mat I) (hH : H.IsHermitian)
    (homega : QAlgorithms.IsDensityMatrix omega) (hfaithful : omega.PosDef) :
    ev omega (entropyProduction H omega) = 0 ∧
    (∀ Theta : Reversal I, Reverses Theta H omega → Theta.map (entropyProduction H omega) = -entropyProduction H omega) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
