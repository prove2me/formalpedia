-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P07_rankTwoCore_signature_swapped
-- name    : QAlgorithms.Papers.Independent.Information100.P07.rankTwoCore_signature_swapped
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:41:54.885855+00:00
-- url     : https://prove2.me/theorems/2fe960d0-09c8-41e5-8286-307e62eab6ca
-- title:
--   Party-swapped occupied 3x2 CES core signature
-- statement:
--   For a positive rank-two operator on C^3 tensor C^2 with CES range and local ranks (3,2), its Alice partial transpose has four positive and two negative eigenvalues and no zero eigenvalues. Invertible local congruence gives the tensor-swapped S21 canonical pencil with positive definite G; its partial-transpose determinant equals det(G)^3 > 0. The space is six-dimensional, not the nine-dimensional ambient qutrit space.
-- source:
--   Complete Classification of Reversible Entanglement Transformations of Two Qutrits, arXiv:2610.05234v1, PDF p. 13, Unnumbered: rank-two 2x3 CES core partial-transpose signature

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P07

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Entanglement

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:2610.05234v1, PDF pp.12–13: the party-swapped occupied 3 by 2 case of (S21)–(S22).
The canonical columns are exchanged in their two tensor coordinates; the partial transpose remains on Alice. -/
theorem rankTwoCore_signature_swapped (delta : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ)
    (hd : delta.PosSemidef) (hces : IsCES (operatorRange delta))
    (hr : delta.rank = 2) (hlr : localRanks (operatorRange delta) = (3, 2)) :
    let R : Matrix (Fin 3 × Fin 2) (Fin 2) ℂ := fun ij k => pencilColumns (ij.2, ij.1) k
    (Finset.univ.filter (fun i => 0 < ascEigenvalues (partialTransposeFirst delta) i)).card = 4 ∧
    (Finset.univ.filter (fun i => ascEigenvalues (partialTransposeFirst delta) i < 0)).card = 2 ∧
    (∀ i, ascEigenvalues (partialTransposeFirst delta) i ≠ 0) ∧
    ∃ A : Local, ∃ B : Matrix (Fin 2) (Fin 2) ℂ, ∃ G : Matrix (Fin 2) (Fin 2) ℂ,
      IsUnit A ∧ IsUnit B ∧ G.PosDef ∧
      Matrix.kronecker A B * delta * (Matrix.kronecker A B)ᴴ = R * G * Rᴴ ∧
      (partialTransposeFirst (R * G * Rᴴ)).det = G.det ^ 3 ∧ 0 < G.det.re := by sorry

end QAlgorithms.Papers.Independent.Information100.P07

end
