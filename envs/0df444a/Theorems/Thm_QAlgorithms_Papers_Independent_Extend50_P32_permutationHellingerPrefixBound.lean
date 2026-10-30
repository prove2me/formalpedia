-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_permutationHellingerPrefixBound
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.permutationHellingerPrefixBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:00:29.895159+00:00
-- url     : https://prove2.me/theorems/41dcf331-76b2-4832-9401-0f30f8b03e79
-- title:
--   Lemma 5.3: Permutation Hellinger bound by prefix deficits
-- statement:
--   Let $d\ge1$ and let $\alpha_1\ge\cdots\ge\alpha_d>0$ be real numbers, with no sum-one requirement. Let $\pi$ be a permutation of $[d]$ and put $\beta_i=\alpha_{\pi(i)}$. Square roots are nonnegative real roots.
--
--   $$
--   \sum_{i=1}^d(\sqrt{\alpha_i}-\sqrt{\beta_i})^2\le2\sum_{j=1}^{d-1}\frac{\alpha_j-\alpha_{j+1}}{\alpha_j}\sum_{i=1}^j(\alpha_i-\beta_i).
--   $$
--
--   This isolates the source comparison or construction with all of its domain and occurrence conventions retained.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 24, Lemma 5.3

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

/-- Lemma 5.3, PDF p.24: positive ordered real list, not necessarily a
probability distribution; beta is an actual permutation of alpha. -/
theorem permutationHellingerPrefixBound {d : ℕ} (hd : 0 < d) (alpha : Fin d → ℝ)
    (hSorted : Antitone alpha) (hPositive : ∀ i, 0 < alpha i) (pi : Equiv.Perm (Fin d)) :
    h2 d alpha (fun i => alpha (pi i)) ≤ 2 *
      ∑ j : Fin (d - 1), adjacentProbabilityMultiplier alpha j *
        (prefixMass alpha (j.val + 1) - prefixMass (fun i => alpha (pi i)) (j.val + 1)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
