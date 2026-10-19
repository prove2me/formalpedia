-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P07_productFiber_kernelBound
-- name    : QAlgorithms.Papers.Independent.Information100.P07.productFiber_kernelBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:36:41.810985+00:00
-- url     : https://prove2.me/theorems/6ce0b127-54f2-415f-8f5c-b1a233ee4fec
-- title:
--   Lemma S4: product-fiber kernel dimension bound
-- statement:
--   Let $\omega\ge0$ act on two qutrits, have completely entangled range, and have full local ranks. Then
--   $$\dim\bigl(\ker\omega^\Gamma\cap(a\otimes\mathbb C^3)\bigr)\le1\quad(a\ne0).$$
--   The same assertion holds for $\mathbb C^3\otimes b$ with $b\ne0$. Each product fiber denotes the entire linear subspace obtained by varying the other local vector.
--
--   This bound requires neither unit trace nor negative partial transpose and applies to singular partial transposes.
-- source:
--   Complete Classification of Reversible Entanglement Transformations of Two Qutrits, arXiv:2610.05234v1, PDF p. 14, Lemma S4: product-fiber kernel dimension bound

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P07

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Entanglement

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:2610.05234v1, PDF p.14, Lemma S4: both product fibers, without normalization or NPT. -/
theorem productFiber_kernelBound (omega : Joint) (ho : omega.PosSemidef)
    (hces : IsCES (operatorRange omega)) (hr : localRanks (operatorRange omega) = (3, 3)) :
    (∀ a : EuclideanSpace ℂ (Fin 3), a ≠ 0 →
      Module.finrank ℂ ((LinearMap.ker (Matrix.toEuclideanLin (partialTransposeFirst omega))) ⊓
        Submodule.span ℂ {y | ∃ b : EuclideanSpace ℂ (Fin 3), y = tensorVec a b} : Submodule ℂ Space) ≤ 1) ∧
    (∀ b : EuclideanSpace ℂ (Fin 3), b ≠ 0 →
      Module.finrank ℂ ((LinearMap.ker (Matrix.toEuclideanLin (partialTransposeFirst omega))) ⊓
        Submodule.span ℂ {y | ∃ a : EuclideanSpace ℂ (Fin 3), y = tensorVec a b} : Submodule ℂ Space) ≤ 1) := by sorry

end QAlgorithms.Papers.Independent.Information100.P07

end
