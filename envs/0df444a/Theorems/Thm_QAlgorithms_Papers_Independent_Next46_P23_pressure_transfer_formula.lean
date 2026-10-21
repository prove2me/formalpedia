-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_pressure_transfer_formula
-- name    : QAlgorithms.Papers.Independent.Next46.P23.pressure_transfer_formula
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:53:04.33921+00:00
-- url     : https://prove2.me/theorems/8e78f94a-3608-429c-8121-22e5e62f012c
-- title:
--   Theorem 3.6
-- statement:
--   For a nonzero finite-dimensional quantum dynamical system with faithful normalized $\omega$, let $\xi_\omega=\sqrt\omega$ and $U_q(t)=e^{-itL_q}$. For $0\le\alpha\le1$, every finite $p\ge1$ and real $t$, $$e_{p,t}(\alpha)=\log\|U_{p/\alpha}(t)\xi_\omega\|_{\omega,p}^{p},\qquad e_{2,t}(\alpha)=\log(\xi_\omega\mid U_{1/\alpha}(t)\xi_\omega).$$ At $\alpha=0$ both divided exponents mean infinity, using extended exponent arithmetic. The norm is independently defined by modular maximization and duality.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 77, Theorem 3.6

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

/-- Theorem3.6, including alpha=0 via extended division p/0=infinity;
source PDF p.77. The separately stated p=2 formula uses exponent 1/alpha. -/
theorem pressure_transfer_formula [Nonempty I] (H omega : Mat I) (hH : H.IsHermitian)
    (homega : QAlgorithms.IsDensityMatrix omega) (hfaithful : omega.PosDef)
    (a t : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    (∀ p : ℝ, 1 ≤ p → pressure H omega (ENNReal.ofReal p) t a =
      Real.log ((amNorm omega (ENNReal.ofReal p)
        (transfer H omega (ENNReal.ofReal p / ENNReal.ofReal a) t
          (supportPower omega (1/2)))) ^ p)) ∧
    pressure H omega 2 t a = Real.log
      (((supportPower omega (1/2))ᴴ *
        transfer H omega ((ENNReal.ofReal a)⁻¹) t (supportPower omega (1/2))).trace.re) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
