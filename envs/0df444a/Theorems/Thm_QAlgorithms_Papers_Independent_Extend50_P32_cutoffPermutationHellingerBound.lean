-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_cutoffPermutationHellingerBound
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.cutoffPermutationHellingerBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:01:53.697102+00:00
-- url     : https://prove2.me/theorems/ecdad0ed-ccd7-41f9-b70d-5b956ca55ced
-- title:
--   Corollary 5.5: Cutoff version of the permutation Hellinger bound
-- statement:
--   Let $\alpha_1\ge\cdots\ge\alpha_d\ge0$ be real numbers, not necessarily normalized. Let $1\le k<d$ and $\alpha_k>\zeta\ge\alpha_{k+1}$ with $\zeta>0$. Let $\beta_i=\alpha_{\pi(i)}$ for a permutation $\pi$. Set $\alpha_i^\prime=\alpha_i$ for $i\le k$ and $\alpha_{k+1}^\prime=\zeta$.
--
--   $$
--   \sum_{i=1}^d(\sqrt{\alpha_i}-\sqrt{\beta_i})^2\le4\sum_{j=1}^k\frac{\alpha_j^\prime-\alpha_{j+1}^\prime}{\alpha_j^\prime}\sum_{i=1}^j(\alpha_i-\beta_i)+d\zeta+8kL\zeta,\qquad L=\min\{k,\ln(\alpha_1/\zeta)\}.
--   $$
--
--   This isolates the source comparison or construction with all of its domain and occurrence conventions retained.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 25, Corollary 5.5

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

/-- Corollary 5.5, PDF p.25: nonnegative scalar list, no probability
normalization. Positive zeta is the domain of the printed logarithm and
of the positive floored list. No log/division defaults at zeta=0 are used. -/
theorem cutoffPermutationHellingerBound {d : ℕ} (hd : 0 < d) (alpha : Fin d → ℝ)
    (hSorted : Antitone alpha) (hNonneg : ∀ i, 0 ≤ alpha i) (pi : Equiv.Perm (Fin d))
    (k : ℕ) (hk : 1 ≤ k) (hkd : k < d) (zeta : ℝ) (hzeta : 0 < zeta)
    (hAbove : zeta < alpha ⟨k - 1, by omega⟩) (hBelow : alpha ⟨k, hkd⟩ ≤ zeta) :
    h2 d alpha (fun i => alpha (pi i)) ≤
      4 * (∑ j : Fin k,
        ((flooredEntry alpha zeta j.val - flooredEntry alpha zeta (j.val + 1)) /
          flooredEntry alpha zeta j.val) *
          (prefixMass alpha (j.val + 1) - prefixMass (fun i => alpha (pi i)) (j.val + 1))) +
      d * zeta + 8 * k * min (k : ℝ) (Real.log (alpha ⟨0, hd⟩ / zeta)) * zeta := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
