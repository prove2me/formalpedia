-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P16_proposition11
-- name    : QAlgorithms.Papers.Independent.Claimed50.P16.proposition11
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:55:52.073985+00:00
-- url     : https://prove2.me/theorems/368b117a-dd84-4ddb-a463-819beecb8371
-- title:
--   Proposition 11 and its immediate countable-decomposition consequence
-- statement:
--   In Fourier coordinates for normalized circle $L^2$, let $u,v\in\ell^2(\mathbb Z)$ be unit vectors with every Fourier coefficient nonzero. Let $V_x$ act by the positive phase $e^{imx}$ on Fourier mode $m$. Define the separable density state
--
--   $$\rho_{12}=\int_0^{2\pi}V_x|u\rangle\langle u|V_x^*\otimes V_x|v\rangle\langle v|V_x^*\,\frac{dx}{2\pi}.$$
--
--   Then $\rho_{12}-\lambda\sigma$ is not positive for every $\lambda>0$ and every normalized pure state $\sigma$ of finite Schmidt rank. Consequently every positive-weight component in every countable pure decomposition of $\rho_{12}$ has infinite Schmidt rank.
--
--   This is stronger than failure of countable product decomposability.
-- source:
--   The Schmidt number and partially entanglement breaking channels in infinite dimensions, arXiv:1110.4363v3, PDF p. 15, Proposition 11 and its immediate countable-decomposition consequence

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P16

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P16

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsTraceClass traceSize traceClosure rankOne
   productCoeff IsBarycenter IsTraceClosed tensorApply IsSeparable)

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Frontier18.P01 (traceSecond traceFirst)

open QAlgorithms.Papers.Independent.Frontier18.P07 (pureStates)

/-- arXiv:1110.4363v3, PDF pp.15–17, Proposition 11 and its countable-decomposition
consequence. The twirl is (9), with the source's positive Fourier phase. -/
theorem proposition11 (u v : Hilbert ℤ) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huc : ∀ i, u i ≠ 0) (hvc : ∀ i, v i ≠ 0) :
    ∃ rho : State (ℤ × ℤ), rho.coefficients = circleState u v ∧
      IsSeparable rho.coefficients ∧ noFinitePurePart rho ∧ allEnsembleRanksInfinite rho := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P16

end
