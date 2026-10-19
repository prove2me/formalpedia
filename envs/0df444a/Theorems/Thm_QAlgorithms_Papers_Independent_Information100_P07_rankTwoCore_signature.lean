-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P07_rankTwoCore_signature
-- name    : QAlgorithms.Papers.Independent.Information100.P07.rankTwoCore_signature
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:41:18.575999+00:00
-- url     : https://prove2.me/theorems/1811c91e-7060-4a87-b94e-aa23e56977a8
-- title:
--   Unnumbered: rank-two 2x3 CES core partial-transpose signature
-- statement:
--   Let $\delta\ge0$ on its occupied $\mathbb C^2\otimes\mathbb C^3$ space have rank two, completely entangled range, and local ranks $(2,3)$. Its partial transpose has four positive and two negative eigenvalues and no zero eigenvalues on this occupied space. There exist invertible local operators taking it to $RGR^\dagger$, where $G>0$ is two by two and $R=(|00\rangle+|11\rangle,|01\rangle+|12\rangle)$. In this form,
--   $$\det((RGR^\dagger)^\Gamma)=\det(G)^3>0.$$
--
--   This is nonsingularity on the occupied six-dimensional rectangle. Embedding it in the two-qutrit space adds three zero eigenvalues; ambient nonsingularity is not asserted. The supporting declaration states the party-swapped occupied 3 by 2 case, with the same inertia and determinant and with both tensor coordinates of the canonical columns exchanged.
-- source:
--   Complete Classification of Reversible Entanglement Transformations of Two Qutrits, arXiv:2610.05234v1, PDF p. 13, Unnumbered: rank-two 2x3 CES core partial-transpose signature

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P07

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Entanglement

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:2610.05234v1, PDF p.13, Eqs.(S21)–(S22): normal form and occupied-space inertia. -/
theorem rankTwoCore_signature (delta : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ)
    (hd : delta.PosSemidef) (hces : IsCES (operatorRange delta))
    (hr : delta.rank = 2) (hlr : localRanks (operatorRange delta) = (2, 3)) :
    (Finset.univ.filter (fun i => 0 < ascEigenvalues (partialTransposeFirst delta) i)).card = 4 ∧
    (Finset.univ.filter (fun i => ascEigenvalues (partialTransposeFirst delta) i < 0)).card = 2 ∧
    (∀ i, ascEigenvalues (partialTransposeFirst delta) i ≠ 0) ∧
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, ∃ B : Local, ∃ G : Matrix (Fin 2) (Fin 2) ℂ,
      IsUnit A ∧ IsUnit B ∧ G.PosDef ∧
      Matrix.kronecker A B * delta * (Matrix.kronecker A B)ᴴ = pencilColumns * G * pencilColumnsᴴ ∧
      (partialTransposeFirst (pencilColumns * G * pencilColumnsᴴ)).det = G.det ^ 3 ∧ 0 < G.det.re := by sorry

end QAlgorithms.Papers.Independent.Information100.P07

end
