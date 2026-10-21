-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_modular_fluctuation
-- name    : QAlgorithms.Papers.Independent.Next46.P23.modular_fluctuation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:54:31.569079+00:00
-- url     : https://prove2.me/theorems/a9a2c526-3427-46a9-87ac-caec02c412c5
-- title:
--   Proposition 3.7
-- statement:
--   For a nonzero finite-dimensional TRI quantum dynamical system with faithful normalized $\omega$ and $t\ne0$, let $Q_t$ be the spectral law of $-t^{-1}\log\Delta_{\omega_t\mid\omega}$ in $\sqrt\omega$, and let $r(s)=-s$. Then $$r_*Q_t(ds)=e^{-ts}Q_t(ds),\qquad r_*Q_t\sim Q_t.$$ This is an equality of measures and mutual absolute continuity, hence a Radon–Nikodym identity almost everywhere; no ratio at zero-mass atoms is asserted.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 78, Proposition 3.7

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

/-- Proposition3.7, measure-level reflection density, source PDF p.78.
It asserts no pointwise density away from the support; t is nonzero. -/
theorem modular_fluctuation [Nonempty I] (H omega : Mat I) (hH : H.IsHermitian)
    (homega : QAlgorithms.IsDensityMatrix omega) (hfaithful : omega.PosDef)
    (htri : TRI H omega) (t : ℝ) (ht : t ≠ 0) :
    let Q := modularLaw (evolved H omega t) omega t
    Measure.map (fun s : ℝ => -s) Q =
      Q.withDensity (fun s => ENNReal.ofReal (Real.exp (-t*s))) ∧
    Measure.map (fun s : ℝ => -s) Q ≪ Q ∧ Q ≪ Measure.map (fun s : ℝ => -s) Q := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
