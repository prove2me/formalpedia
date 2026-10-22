-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P03_azuma_tail
-- name    : QAlgorithms.Papers.Independent.Gap20.P03.azuma_tail
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:14:25.593465+00:00
-- url     : https://prove2.me/theorems/af086873-8832-4613-9c0a-3e7e6d55681b
-- title:
--   Lemma 2.3: Azuma tail bound
-- statement:
--   Let $R_1,\ldots,R_n$ be measurable real martingale differences on a probability space: each increment is integrable and has conditional expectation zero given all previous increments. Suppose $|R_i|\le c$ almost surely. For $c>0$ and $\lambda>0$,
--   $$\Pr\!\left[\sum_{i=1}^nR_i\ge\lambda n\right]\le\exp\!\left(-\frac{\lambda^2n}{2c^2}\right).$$
--   For $c=0$, the same event has probability zero when $n>0$ and probability one when $n=0$. This is the concentration estimate used for classical entropy accumulation; the degenerate case does not evaluate a division by zero.
-- source:
--   A Tight High-Order Entropic Quantum Uncertainty Relation With Applications, arXiv:quant-ph/0612014v2, PDF p. 6, Lemma 2.3: Azuma tail bound

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable

/-- Lemma 2.3, p.6: positive-c Azuma bound, and the deterministic c=0
interpretation separately. n=0 has the probability-one empty-sum event. -/
theorem azuma_tail {W : Type*} [MeasurableSpace W] (mu : Measure W)
    [IsProbabilityMeasure mu] (n : ℕ) (R : Fin n → W → ℝ)
    (hR : MartingaleDifferences mu R) (c lambda : ℝ) (hc : 0 ≤ c)
    (hbounded : ∀ i, ∀ᵐ w ∂mu, |R i w| ≤ c) (hlambda : 0 < lambda) :
    (0 < c → mu {w | lambda*n ≤ ∑ i, R i w} ≤
      ENNReal.ofReal (Real.exp (-(lambda^2*n)/(2*c^2)))) ∧
    (c = 0 → mu {w | lambda*n ≤ ∑ i, R i w} = if n = 0 then 1 else 0) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P03

end
