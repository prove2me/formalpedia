-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_renyi_zero_tv
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.renyi_zero_tv
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:52:27.322734+00:00
-- url     : https://prove2.me/theorems/a976605d-1797-494c-af91-93573dffa6e1
-- title:
--   Remark 49: tight order-zero Renyi/TV bound (504)
-- statement:
--   For $P\ll Q$ with $|P-Q|<2$,
--
--   $$D_0(P\|Q)\le-\log_b(1-|P-Q|/2).$$
--
--   For a finite probability law $Q$ and event $F$ of mass $1-\delta$, $0\le\delta<1$, the conditional law $P=Q(\cdot\mid F)$ has $|P-Q|=2\delta$ and $D_0=-\log_b(1-\delta)$, attaining equality. Order-zero divergence uses (77), rather than the older identically-zero convention.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 70, Remark 49

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Remark 49: tight order-zero Renyi/TV bound (504). Sason--Verdu, arXiv:1508.00335v7, PDF p.70.  -/
theorem renyi_zero_tv
    (b : LogBase) {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q) (hv : fullVariation P Q < 2) :
    renyiDiv b 0 P Q ≤ (-logB b (1 - (fullVariation P Q).toReal / 2) : ℝ) ∧
    (∀ (n : ℕ) (p : Fin n → ℝ) (F : Finset (Fin n)) (d : ℝ),
      0 ≤ d → d < 1 → (∀ i, 0 ≤ p i) → (∑ i, p i) = 1 → (∑ i ∈ F, p i) = 1 - d →
      let Q0 : Measure (Fin n) := ∑ i, ENNReal.ofReal (p i) • Measure.dirac i
      let P0 : Measure (Fin n) := ∑ i, ENNReal.ofReal (if i ∈ F then p i / (1 - d) else 0) • Measure.dirac i
      IsProbabilityMeasure P0 ∧ IsProbabilityMeasure Q0 ∧ P0 ≪ Q0 ∧
      fullVariation P0 Q0 = ENNReal.ofReal (2 * d) ∧ renyiDiv b 0 P0 Q0 = (-logB b (1 - d) : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
