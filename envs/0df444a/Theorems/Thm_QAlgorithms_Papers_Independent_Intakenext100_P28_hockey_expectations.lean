-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_hockey_expectations
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.hockey_expectations
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:40:26.955489+00:00
-- url     : https://prove2.me/theorems/1a6f5820-9eab-4867-89de-df182a17ddcf
-- title:
--   Theorem 31: E_Q|density-gamma|=2E_gamma+gamma-1; E_Q max(gamma,density)=gamma+E_gamma; E_Q min(gamma,density)=1-E_gamma
-- statement:
--   For $P\ll Q$, $Z=dP/dQ$, and $\gamma\ge1$,
--
--   $$E_Q|Z-\gamma|=2E_\gamma(P\|Q)+\gamma-1,\quad
--   E_Q\max\{\gamma,Z\}=\gamma+E_\gamma(P\|Q),\quad
--   E_Q\min\{\gamma,Z\}=1-E_\gamma(P\|Q).$$
--
--   All three identities (409)–(411) are included. Normalization gives $E_Q Z=1$.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 58, Theorem 31

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 31: E_Q|rnDensityReal-gamma|=2E_gamma+gamma-1; E_Q max(gamma,rnDensityReal)=gamma+E_gamma; E_Q min(gamma,rnDensityReal)=1-E_gamma. Sason--Verdu, arXiv:1508.00335v7, PDF p.58.  -/
theorem hockey_expectations
    {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q) (g : ℝ) (hg : 1 ≤ g) :
    (∫⁻ x, ENNReal.ofReal |rnDensityReal P Q x - g| ∂Q) = 2 * hockey g P Q + ENNReal.ofReal (g - 1) ∧
    (∫⁻ x, ENNReal.ofReal (max g (rnDensityReal P Q x)) ∂Q) = ENNReal.ofReal g + hockey g P Q ∧
    (∫⁻ x, ENNReal.ofReal (min g (rnDensityReal P Q x)) ∂Q) = 1 - hockey g P Q := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
