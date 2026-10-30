-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P16_optimizedEnergyBound
-- name    : QAlgorithms.Papers.Independent.Bridge50.P16.optimizedEnergyBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:45:31.986726+00:00
-- url     : https://prove2.me/theorems/2bf469c3-a2ce-4155-9ee3-ce31f8e982f2
-- title:
--   Theorem 12, Eqs.(38)–(41), Appendix C: optimized constrained bound
-- statement:
--   Let $0\le\eta\le1$, $b\ge0$, $E\ge0$, and $t=\eta-(1-\eta)b>0$. For $G_1\in I=[1,1+(1-\eta)b]$, define
--
--   $$\bar\eta=1-\frac{(1-\eta)(b+1)}{G_1},\quad G_2=\frac{\eta}{G_1-(1-\eta)(b+1)},\quad E_2=G_2E+G_2-1,$$
--   $$f(G_1)=\max\{g(\bar\eta E_2)-g((1-\bar\eta)E_2),0\},\qquad g(x)=(1+x)\log_2(1+x)-x\log_2x.$$
--
--   There exists $G_1^*\in I$ minimizing $f$ on $I$, and
--
--   $$Q_E(\mathcal N[\eta,b])\le f(G_1^*)=\min_{G_1\in I} f(G_1).$$
--
--   At that gain the exact channel decomposition is $\mathcal N[\eta,b]=\mathcal A[G_1^*]\circ\mathcal N[\bar\eta,0]\circ\mathcal A[G_2]$. The budget refers to the mean encoded maximally mixed state. This gives the optimized bound without asserting numerical endpoint optimality.
-- source:
--   Improved quantum capacity bounds of Gaussian loss channels and achievable rates with Gottesman-Kitaev-Preskill codes, arXiv:1801.07271v2, PDF p. 7, Theorem 12, Eqs.(38)–(41), Appendix C: optimized constrained bound

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

/-- Theorem 12, PDF p.7 Eqs.(38)--(41), Appendix C p.16. A minimizing gain
in the compact physical interval is attained; no numerical endpoint claim. -/
theorem optimizedEnergyBound (eta b budget : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1)
    (hb : 0 ≤ b) (hbudget : 0 ≤ budget) (ht : 0 < eta - (1 - eta) * b) :
    ∃ gain ∈ Set.Icc 1 (1 + (1 - eta) * b),
      (∀ other ∈ Set.Icc 1 (1 + (1 - eta) * b),
        optimizedObjective eta b budget gain ≤ optimizedObjective eta b budget other) ∧
      energyCapacity (coefficientChannel (C.thermal eta b)) budget ≤
        ENNReal.ofReal (optimizedObjective eta b budget gain) ∧
      (∀ X, B.IsTraceClass X → C.thermal eta b X =
        C.amplifier gain (C.thermal (1 - (1 - eta) * (b + 1) / gain) 0
          (C.amplifier (eta / (gain - (1 - eta) * (b + 1))) X))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P16

end
