-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P23_orthogonal_projectiveImplementation
-- name    : QAlgorithms.Papers.Independent.Intake100.P23.orthogonal_projectiveImplementation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:12:55.649224+00:00
-- url     : https://prove2.me/theorems/a7a2ed15-a21a-46b0-9c01-1e415ff471a4
-- title:
--   Projective orthogonal implementation
-- statement:
--   Let $Y$ be a finite even-dimensional real Hilbert space and $\phi:Y\to B(H)$ an irreducible CAR representation on a nonzero complex Hilbert space. Every orthogonal automorphism $r$ has a unitary implementer, unique up to a scalar of modulus one:
--   $$U_r\phi(y)U_r^*=\phi(ry).$$
--   The resulting phase classes form a group homomorphism,
--   $$[U_r][U_s]=[U_{rs}]\quad\text{in }\mathcal U(H)/\mathcal U(1).$$
--   This describes orthogonal covariance without choosing a sign lift. **Formalization Note** The last identity is expressed equivalently for arbitrary unitary representatives of these classes.
-- source:
--   Introduction to representations of the canonical commutation and anticommutation relations, arXiv:math-ph/0511030v2, PDF p. 17, Theorem 11

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P23

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P23

open QAlgorithms.Papers.Independent.Renew46.P03 (tensorVector)

variable {Y : Type*} [AddCommGroup Y] [Module ℝ Y]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section CAR

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- PDF p.17, Theorem 11: existence, scalar uniqueness, and multiplication of
orthogonal implementer classes; all standing assumptions of Section 4.3 included. -/
theorem orthogonal_projectiveImplementation [CompleteSpace E] [FiniteDimensional ℝ E]
    [Nontrivial H] (heven : Even (Module.finrank ℝ E))
    (phi : E → H →L[ℂ] H) (hphi : IsCAR phi) (hi : HilbertIrreducible phi) :
    (∀ r : E ≃ₗᵢ[ℝ] E,
      ∃ U : H →L[ℂ] H, U ∈ unitary (H →L[ℂ] H) ∧ ConjugatesCAR phi r U ∧
        ∀ V : H →L[ℂ] H, V ∈ unitary (H →L[ℂ] H) → ConjugatesCAR phi r V → SamePhase U V) ∧
    (∀ (r s : E ≃ₗᵢ[ℝ] E) (U V T : H →L[ℂ] H),
      U ∈ unitary (H →L[ℂ] H) → V ∈ unitary (H →L[ℂ] H) → T ∈ unitary (H →L[ℂ] H) →
      ConjugatesCAR phi r U → ConjugatesCAR phi s V →
      ConjugatesCAR phi (fun y => r (s y)) T → SamePhase (U * V) T) := by sorry

end CAR

end QAlgorithms.Papers.Independent.Intake100.P23

end
