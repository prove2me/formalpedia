-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P28_thermalGapLemma
-- name    : QAlgorithms.Papers.Independent.Bridge50.P28.thermalGapLemma
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:30:18.093018+00:00
-- url     : https://prove2.me/theorems/2a61889a-3323-4e18-9404-eb712fbd3290
-- title:
--   Lemma 1, including (i), (ii) and Eq. (4)
-- statement:
--   With natural logarithms, let $g(x)=(x+1)\ln(x+1)-x\ln x$, using $0\ln0=0$. Fix a positive real $Y$ and define $\Delta_Y(X)=g(X/(Y+1))-g(X+Y)+g(Y)$. Then
--
--   $$
--   \lim_{X\to+\infty}\Delta_Y(X)=Y\ln(1+Y^{-1})<1,
--   \qquad \Delta_Y'(X)>0\quad(X>0).
--   $$
--
--   In particular, for every positive real $X$,
--
--   $$
--   \Delta_Y(X)<Y\ln(1+Y^{-1})<1.
--   $$
--
--   This scalar lemma supplies both the universal additive capacity estimate and its noise-dependent refinement. The formal statement uses an actual limit and existence of a positive derivative via a derivative certificate, avoiding any default derivative value at a nondifferentiable point.
-- source:
--   The classical capacity of quantum thermal noise channels to within 1.45 bits, arXiv:1207.0256v1, PDF p. 2, Lemma 1, including (i), (ii) and Eq. (4)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P28

open Filter

open scoped BigOperators NNReal ENNReal Topology

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel)

open QAlgorithms.Papers.Independent.Frontier18.P18
  (operatorCoeff boundedOperator)

open QAlgorithms.Papers.Independent.Claimed50.P35
  (traceClassChannelPower tracePair)

open QAlgorithms.Papers.Independent.Gap48.P26 (weightedPhotonExpectation)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- Lemma 1, PDF p.2: clauses (i), (ii), and the full strict chain (4).
A real Tendsto states the limit; HasDerivAt excludes a default-zero derivative
at nondifferentiable points. No proof derivative or asymptotic is a hypothesis. -/
theorem thermalGapLemma (Y : ℝ) (hY : 0 < Y) :
    Tendsto (thermalBoundGapNats Y) atTop (𝓝 (Y * Real.log (1 + Y⁻¹))) ∧
    Y * Real.log (1 + Y⁻¹) < 1 ∧
    (∀ X : ℝ, 0 < X → ∃ d : ℝ,
      HasDerivAt (thermalBoundGapNats Y) d X ∧ 0 < d) ∧
    (∀ X : ℝ, 0 < X →
      thermalBoundGapNats Y X < Y * Real.log (1 + Y⁻¹)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P28

end
