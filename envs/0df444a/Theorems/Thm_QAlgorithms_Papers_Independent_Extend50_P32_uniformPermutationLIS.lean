-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_uniformPermutationLIS
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.uniformPermutationLIS
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:06:58.235283+00:00
-- url     : https://prove2.me/theorems/7dbd1edd-5646-4b65-acaa-79b28a71c54b
-- title:
--   Unnumbered: Expected LIS of a uniform random permutation
-- statement:
--   For an integer $n\ge0$, let $\pi$ be uniform over permutations of $[n]$. Write $\operatorname{LIS}(\pi)$ for its longest increasing subsequence length, equivalently its first RSK row. For $n=0$ the unique permutation and its subsequence are empty.
--
--   $$
--   \mathbb E_{\pi\sim\operatorname{Unif}(S_n)}\operatorname{LIS}(\pi)\le2\sqrt n\qquad(n\ge0).
--   $$
--
--   This isolates the source comparison or construction with all of its domain and occurrence conventions retained.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 2, Unnumbered

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

/-- Unnumbered main corollary, PDF pp.2-3: uniform-permutation expected LIS.
The paper gives a new proof of the VK85/Pil90 bound; n=0 is included. -/
theorem uniformPermutationLIS (n : ℕ) :
    ((Fintype.card (Equiv.Perm (Fin n)) : ℝ))⁻¹ *
      (∑ pi : Equiv.Perm (Fin n), row (shape (List.ofFn (fun i => pi i))) 0) ≤
      2 * Real.sqrt n := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
