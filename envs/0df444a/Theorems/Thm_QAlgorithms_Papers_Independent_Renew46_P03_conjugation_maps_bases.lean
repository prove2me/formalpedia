-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P03_conjugation_maps_bases
-- name    : QAlgorithms.Papers.Independent.Renew46.P03.conjugation_maps_bases
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:53:49.431449+00:00
-- url     : https://prove2.me/theorems/4a83a99a-1aa1-4d5e-bf0c-09a9dbb58dae
-- title:
--   Unnumbered consequence: conjugation sends ONBs to ONBs
-- statement:
--   Let $H$ be a separable complex Hilbert space and $K:H\to H$ a bounded conjugate-linear map fixing a complete countable orthonormal basis. For every complete countable orthonormal basis $(b_i)_{i\in I}$ of $H$, there is a complete orthonormal basis $(c_i)_{i\in I}$ satisfying
--
--   $$c_i=K(b_i)\qquad(i\in I).$$
--
--   Thus the image family is complete, as well as orthonormal. Finite and empty index sets are allowed.
-- source:
--   Operator Isomorphisms on Hilbert Space Tensor Products, arXiv:2010.15901v1, PDF p. 4, Unnumbered consequence

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P03

universe u v

open QAlgorithms.Papers.Independent.Claimed50.P34 (HilbertTensor)

/-- Unnumbered consequence of Corollary 1.4(c), PDF p.4: a conjugation
sends every complete orthonormal basis to a complete orthonormal basis. -/
theorem conjugation_maps_bases
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (K : H →L⋆[ℂ] H) (hK : IsConjugation K)
    {ι : Type v} [Countable ι] (b : HilbertBasis ι ℂ H) :
    ∃ c : HilbertBasis ι ℂ H, ∀ i, c i = K (b i) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P03

end
