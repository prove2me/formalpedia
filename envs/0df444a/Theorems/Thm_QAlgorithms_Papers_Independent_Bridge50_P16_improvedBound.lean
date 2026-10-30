-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P16_improvedBound
-- name    : QAlgorithms.Papers.Independent.Bridge50.P16.improvedBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:44:06.020985+00:00
-- url     : https://prove2.me/theorems/73dfb475-580c-4e7b-aa31-8010330e0840
-- title:
--   Theorem 10, Eqs.(31)–(32): improved unconstrained bound
-- statement:
--   Let $0<\eta<1$, $b\ge0$ and $t=\eta-(1-\eta)b>0$. The energy-unconstrained operational quantum capacity obeys
--
--   $$Q(\mathcal N[\eta,b])\le Q(\mathcal N[t,0])=\max\!\left\{\log_2\frac{\eta-(1-\eta)b}{(1-\eta)(b+1)},0\right\}.$$
--
--   Capacities are in qubits per mode. The hypotheses make the logarithm and finite pre-amplifier decomposition physical. This is the improved data-processing bound, independently obtained in [19], Eqs.(39),(40).
-- source:
--   Improved quantum capacity bounds of Gaussian loss channels and achievable rates with Gottesman-Kitaev-Preskill codes, arXiv:1801.07271v2, PDF p. 6, Theorem 10, Eqs.(31)–(32): improved unconstrained bound

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P16

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal NNReal Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P16

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)

open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P32 (CPTP applyChoi)

/-- Theorem 10, PDF p.6 Eqs.(31)--(32); independent [19] Eqs.(39),(40).
The printed real logarithm and finite decomposition are used only for 0<t<1. -/
theorem improvedBound (eta b : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (hb : 0 ≤ b)
    (ht : 0 < eta - (1 - eta) * b) :
    T.operationalTraceClassCapacity (coefficientChannel (C.thermal eta b)) ≤
      T.operationalTraceClassCapacity (coefficientChannel (C.thermal (eta - (1 - eta) * b) 0)) ∧
    T.operationalTraceClassCapacity (coefficientChannel (C.thermal (eta - (1 - eta) * b) 0)) =
      ENNReal.ofReal (max (Real.logb 2 ((eta - (1 - eta) * b) / ((1 - eta) * (b + 1)))) 0) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P16

end
