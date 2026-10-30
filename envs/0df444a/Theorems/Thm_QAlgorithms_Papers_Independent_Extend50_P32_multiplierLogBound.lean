-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_multiplierLogBound
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.multiplierLogBound
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T10:01:12.333735+00:00
-- url     : https://prove2.me/theorems/48d6e046-e6d5-4ee9-8585-205165e4a35d
-- title:
--   Lemma 5.4: Multiplier sum logarithmic bound
-- statement:
--   Let $d\ge1$ and let $\alpha_1\ge\cdots\ge\alpha_d>0$ be real numbers, with no probability normalization. The logarithm is natural. At $d=1$ the sum is empty.
--
--   $$
--   \sum_{i=1}^{d-1}\frac{\alpha_i-\alpha_{i+1}}{\alpha_i}\le\min\left\{d,\ln\frac{\alpha_1}{\alpha_d}\right\}.
--   $$
--
--   This isolates the source comparison or construction with all of its domain and occurrence conventions retained.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 24, Lemma 5.4

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P32

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Matrix ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Extend50.P32

open QAlgorithms.Papers.Independent.Support50.P38 (wordMass tv)

-- For the density matrices below, the characteristic-polynomial identity
-- preserves all eigenvalues with multiplicity and is equivalent to unitary
-- diagonalization with these real eigenvalues. No accuracy is assumed.

open QAlgorithms.Papers.Independent.Gap20.P17 (HasSpectrum)

/-- Lemma 5.4, PDF p.24: the printed upper bound is d, not d-1;
at d=1 the sum and log(1) are both zero. -/
theorem multiplierLogBound {d : ℕ} (hd : 0 < d) (alpha : Fin d → ℝ)
    (hSorted : Antitone alpha) (hPositive : ∀ i, 0 < alpha i) :
    (∑ j : Fin (d - 1), adjacentProbabilityMultiplier alpha j) ≤
      min (d : ℝ) (Real.log (alpha ⟨0, hd⟩ / alpha ⟨d - 1, by omega⟩)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
