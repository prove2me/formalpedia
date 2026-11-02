-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_orthogonal_representation_exists
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.orthogonal_representation_exists
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:56:51.31572+00:00
-- url     : https://prove2.me/theorems/a5fc30dd-9684-45e5-a1be-ce04477d06ba
-- title:
--   Existence of orthogonal representations (supporting Lemma 3.6)
-- statement:
--   For an abelian concrete von Neumann algebra, every element in the complex linear span of its nonzero projections admits a finite sum of pairwise orthogonal nonzero projections with complex coefficients. Zero coefficients are allowed. The zero element admits the empty representation.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 60, Unnumbered construction preceding Lemma 3.6

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- orthogonal-representation-existence; de Groote, Observables I, PDF pp. 59, 60.
Restored in moderation: source background status is not a formalization obstacle. -/
theorem orthogonal_representation_exists {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (R : VonNeumannAlgebra H)
    (hcomm : ∀ a b : R.toStarSubalgebra, a * b = b * a) (x : R.toStarSubalgebra)
    (hx : x ∈ Submodule.span ℂ {a : R.toStarSubalgebra |
      ∃ p : Projection R, p.val ≠ 0 ∧ (a : H →L[ℂ] H) = p.val}) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (p : Fin n → Projection R),
      IsOrthogonalRepresentation x c p := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
