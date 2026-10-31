-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_nearby_density_reverse_pinsker
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.nearby_density_reverse_pinsker
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:45:25.208899+00:00
-- url     : https://prove2.me/theorems/e19a5f61-4417-45df-b33c-b4f69646ffc4
-- title:
--   Appendix E: two-sided nearby-density reverse Pinsker bounds
-- statement:
--   Let $P\ll Q$ and $0<\eta<1$. If $1-\eta\le dP/dQ\le1+\eta$ almost everywhere, then
--
--   $$D(P\|Q)\le\frac{(1+\eta)\log_b(1+\eta)+(1-\eta)\log_b(1-\eta)}{2\eta}|P-Q|
--   \le\eta\log_b e\,|P-Q|.$$
--
--   Also $|P-Q|\le\eta$, hence $D(P\|Q)\le\eta^2\log_b e$. These are all displayed bounds (612)–(616). Two-sided uniform density control is distinct from the false one-sided local-convergence implication in Appendix C.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 82, Appendix E

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Appendix E: two-sided nearby-rnDensityReal reverse Pinsker bounds. Sason--Verdu, arXiv:1508.00335v7, PDF p.82.  -/
theorem nearby_density_reverse_pinsker
    (b : LogBase) {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q)
    (e : ℝ) (he : 0 < e ∧ e < 1)
    (hd : ∀ᵐ x ∂Q, 1 - e ≤ rnDensityReal P Q x ∧ rnDensityReal P Q x ≤ 1 + e) :
    kl b P Q ≤ ENNReal.ofReal (((1 + e) * logB b (1 + e) +
      (1 - e) * logB b (1 - e)) / (2 * e)) * fullVariation P Q ∧
    ENNReal.ofReal (((1 + e) * logB b (1 + e) +
      (1 - e) * logB b (1 - e)) / (2 * e)) * fullVariation P Q ≤
      ENNReal.ofReal (e * logBaseE b) * fullVariation P Q ∧
    fullVariation P Q ≤ ENNReal.ofReal e ∧ kl b P Q ≤ ENNReal.ofReal (e ^ 2 * logBaseE b) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
