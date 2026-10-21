-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_fcs_identification
-- name    : QAlgorithms.Papers.Independent.Next46.P23.fcs_identification
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:55:52.761777+00:00
-- url     : https://prove2.me/theorems/d3aef043-8cb3-475e-93b1-afc30cc1d2a8
-- title:
--   §3.5: FCS equals relative-modular spectral law
-- statement:
--   For a nonzero finite-dimensional quantum dynamical system with faithful normalized $\omega$, measure $S=-\log\omega$ at times zero and $t\ne0$. The joint weight is $\operatorname{tr}(e^{-itH}\omega P_s e^{itH}P_{s^\prime})$, and let $P_t$ be the law of $(s^\prime-s)/t$. Then $$P_t=Q_{-t},\quad e_{2,-t}(\alpha)=\log\int e^{-t\alpha x}dP_t(x),\quad\mathbb E_{P_t}x=\omega(\Sigma^t),\quad\operatorname{Var}_{P_t}(x)=\omega((\Sigma^t)^2)-\omega(\Sigma^t)^2.$$ The law is a probability measure. Under TRI it also equals $Q_t$ and its reflected law has density $e^{-tx}$. Identification and the first two moments do not require TRI; no higher-cumulant equality is claimed.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 79, §3.5: FCS equals relative-modular spectral law

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

/-- Two-measurement FCS equals Q_(-t), with its mean and variance; source PDF p.79.
No TRI is used for identification or moments. Reflection is conditional. -/
theorem fcs_identification [Nonempty I] (H omega : Mat I) (hH : H.IsHermitian)
    (homega : QAlgorithms.IsDensityMatrix omega) (hfaithful : omega.PosDef)
    (t : ℝ) (ht : t ≠ 0) :
    IsProbabilityMeasure (fcs H omega t) ∧
    fcs H omega t = modularLaw (evolved H omega (-t)) omega (-t) ∧
    (∀ a : ℝ, pressure H omega 2 (-t) a =
      Real.log (∫ x : ℝ, Real.exp (-t*a*x) ∂fcs H omega t)) ∧
    (∫ x : ℝ, x ∂fcs H omega t) = ev omega (averagedProduction H omega t) ∧
    (∫ x : ℝ, x^2 ∂fcs H omega t) - (∫ x : ℝ, x ∂fcs H omega t)^2 =
      ev omega ((averagedProduction H omega t)^2) - ev omega (averagedProduction H omega t)^2 ∧
    (TRI H omega → fcs H omega t = modularLaw (evolved H omega t) omega t ∧
      Measure.map (fun x : ℝ => -x) (fcs H omega t) =
        (fcs H omega t).withDensity (fun x => ENNReal.ofReal (Real.exp (-t*x)))) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
