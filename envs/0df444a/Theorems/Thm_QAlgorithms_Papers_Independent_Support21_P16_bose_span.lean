-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P16_bose_span
-- name    : QAlgorithms.Papers.Independent.Support21.P16.bose_span
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:37:20.012718+00:00
-- url     : https://prove2.me/theorems/e5b0fcbb-3458-431a-a0ee-fab09926fd50
-- title:
--   Tensor powers span the Bose subspace
-- statement:
--   Let $d>0$ and $n\ge1$ be integers. In $H^{\otimes n}$, where $H=\mathbb C^d$ has its fixed orthonormal basis, write $\phi^{\otimes n}(x)=\prod_{j=1}^n\phi_{x_j}$ in tensor-word coordinates. Let $H_n^+$ be the subspace fixed by every permutation of the $n$ factors, and let $P_\pi$ be the actual tensor permutation matrix. Then
--   $$
--   \operatorname{span}_{\mathbb C}\{\phi^{\otimes n}:\phi\in H\}=H_n^+,
--   \qquad s_n=\frac1{n!}\sum_{\pi\in S_n}P_\pi
--   $$
--   is its orthogonal projector: $s_n^*=s_n=s_n^2$, its image lies in $H_n^+$, and it fixes every vector of $H_n^+$.
--
--   This identifies the effective input Hilbert space with a concrete subspace of tensor-word coordinates.
-- source:
--   Optimal Cloning of Pure States, arXiv:quant-ph/9804001v1, PDF p. 5, bose-span

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P16

noncomputable section

open scoped Matrix ComplexOrder

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Support21.P16

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector powerVector IsCloningCovariant haarAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Support21.P16.unitaryMeasurable

/-- PDF p.5, section 3: tensor powers span exactly the permutation-fixed space;
the explicit average is its orthogonal projection. -/
theorem bose_span (d n : ℕ) (hd : 0 < d) (hn : 1 ≤ n) :
    Submodule.span ℂ (Set.range (coherentTensor (d := d) n)) = boseSpace d n ∧
    (boseProjector d n)ᴴ = boseProjector d n ∧
    boseProjector d n * boseProjector d n = boseProjector d n ∧
    (∀ v : TensorSpace d n, QAlgorithms.act (boseProjector d n) v ∈ boseSpace d n) ∧
    (∀ v ∈ boseSpace d n, QAlgorithms.act (boseProjector d n) v = v) := by sorry

end QAlgorithms.Papers.Independent.Support21.P16

end
