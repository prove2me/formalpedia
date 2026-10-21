-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_gibbs_perturbation_bound
-- name    : QAlgorithms.Papers.Independent.Next46.P23.gibbs_perturbation_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:44:09.082446+00:00
-- url     : https://prove2.me/theorems/25364a8a-643e-4964-ba6d-510fa964a7ce
-- title:
--   Proposition 2.22
-- statement:
--   For self-adjoint $H,V$ on a nonzero finite-dimensional complex Hilbert space, real $\beta$ and complex $a$, put $\rho_\beta=e^{-\beta H}/\operatorname{tr}e^{-\beta H}$ and $E_{aV}(z)=e^{iz(H+aV)}e^{-izH}$. Then $$|\rho_\beta(E_{aV}(i\beta))-1|\le e^{|a\beta|\|V\|}-1.$$ The norm is the operator norm. This bound includes $\beta=0$ and $V=0$.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 56, Proposition 2.22

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

/-- Proposition2.22, complex coupling alpha and real beta, source PDF pp.56--57. -/
theorem gibbs_perturbation_bound [Nonempty I] (H V : Mat I) (hH : H.IsHermitian) (hV : V.IsHermitian)
    (beta : ℝ) (a : ℂ) :
    ‖(QAlgorithms.gibbsState ((-(beta : ℂ)) • H) * perturbationCocycle H V a (Complex.I * (beta : ℂ))).trace - 1‖ ≤
      Real.exp (‖a * (beta : ℂ)‖ * QAlgorithms.specNorm V) - 1 := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
