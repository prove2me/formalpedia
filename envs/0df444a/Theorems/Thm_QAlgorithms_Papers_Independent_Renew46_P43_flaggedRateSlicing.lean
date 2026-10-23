-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_flaggedRateSlicing
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.flaggedRateSlicing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:51:31.075087+00:00
-- url     : https://prove2.me/theorems/7ea84855-d1b4-4cd4-8e83-ec391b2cdb3c
-- title:
--   Remark IV.12: Constructed rate-slicing decoder has failure-flag probability≤lambdaBar; on selected codebooks its maximum conditional decoding er
-- statement:
--   For the constructed rate-slicing decoder, the rate and mean-error bounds of rate slicing hold. There is a selected union of codebooks; outside it the decoder flags failure. The first bound below concerns uncovered source words, and the second concerns the normalized conditional channel states on selected words. This is an existence assertion about the constructed decoder, not every low-average-error decoder.
--
--   $$
--   P^{\otimes n}(\text{uncovered words})\le\bar\lambda,\qquad\max_{x^n\ \text{in selected codebooks}}\Pr(\text{wrong}\mid x^n)\le\bar\lambda.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 54, Remark IV.12

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P40 (InBlocks)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P43.matrixMeasurableSpace

/-- Remark IV.12, PDF p.54: a property of a constructed decoder, with uncovered
source mass distinguished from the maximum conditional error inside selected codebooks. -/
theorem flaggedRateSlicing (a d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (lambda delta : ℝ) (hlambda : 0 < lambda) (hdelta : 0 < delta) :
    ∃ n0 : ℕ, 0 < n0 ∧ ∀ (S : HybridSource 1),
      (∀ i, S.alphabet i = a) → S.system.dim = d → ∀ n : ℕ, n0 ≤ n →
      ∃ c : SideCode S n, ∃ covered : Finset (∀ i, Fin n → Fin (S.alphabet i)),
        c.rate 0 ≤ S.subsetEntropy Finset.univ + 3 * delta ∧ c.error ≤ lambda ∧
        (∑ x ∈ (Finset.univ \ covered), ∏ t, S.classicalMass (fun i => x i t)) ≤ lambda ∧
        (∀ x ∈ covered, 1 - effectProb (wordTensor (fun t => S.conditional (fun i => x i t)))
          (c.decode (c.message x) (some x)) ≤ lambda) ∧
        (∀ x, x ∉ covered → c.decode (c.message x) none = 1) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
