-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_permutationSourceCoding
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.permutationSourceCoding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:52:59.427049+00:00
-- url     : https://prove2.me/theorems/d9f8c64f-8405-4139-a09b-4cc3900521ef
-- title:
--   IV.14-permutation-coding: For each ordering pi, all sufficiently large n admit codes with r_pi(i)≤H(X_pi(i)|Y X_pi(1)…X_pi(i−1))+3delta, error≤lambdaBar and
-- statement:
--   Let a finite correlated classical/hybrid source have classical senders $X_1,\ldots,X_s$ and free side information $Y$ at the decoder. For any permutation $\pi$ and $\bar\lambda,\delta>0$, all sufficiently large $n$ admit separate classical encoders and an actual retained-outcome square-root decoding instrument. One length threshold is uniform over source laws at fixed alphabet sizes, output dimension and tolerances.
--
--   $$
--   r_{\pi(i)}\le H(X_{\pi(i)}\mid YX_{\pi(1)}\cdots X_{\pi(i-1)})+3\delta,\quad\bar e\le\bar\lambda,\quad\mathbb E\|\text{ideal labelled }Y^n-\text{recovered labelled }Y^n\|_1\le\bar\lambda.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 55, IV.14-permutation-coding

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

/-- Valid permutation-corner construction inside the proof of IV.14, PDF p.55.
The false simultaneous upper bounds in printed IV.14 are not used. Smaller internal
error parameters ensure the final labelled-Y disturbance is at most lambda. -/
theorem permutationSourceCoding (s : ℕ) (a : Fin s → ℕ) (ha : ∀ i, 0 < a i)
    (d : ℕ) (hd : 0 < d) (lambda delta : ℝ) (hlambda : 0 < lambda) (hdelta : 0 < delta) :
    ∃ n0 : ℕ, 0 < n0 ∧ ∀ (S : HybridSource s), S.alphabet = a → S.system.dim = d →
      ∀ (pi : Equiv.Perm (Fin s)) (n : ℕ), n0 ≤ n →
      ∃ c : SideCode S n, (∀ i, c.rate (pi i) ≤ S.corner pi (pi i) + 3 * delta) ∧
        c.error ≤ lambda ∧ c.disturbance ≤ lambda := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
