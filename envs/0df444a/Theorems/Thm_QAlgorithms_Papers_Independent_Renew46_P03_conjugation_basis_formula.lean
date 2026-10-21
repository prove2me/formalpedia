-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P03_conjugation_basis_formula
-- name    : QAlgorithms.Papers.Independent.Renew46.P03.conjugation_basis_formula
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:50:46.365023+00:00
-- url     : https://prove2.me/theorems/b7a5cd13-6dbd-45d1-a787-0ed7b2c052cc
-- title:
--   Lemma 1.3: formula for a basis conjugation
-- statement:
--   Let $H$ be a separable complex Hilbert space and let $K:H\to H$ be bounded and conjugate-linear. A conjugation means such a map fixing some complete countable orthonormal basis. Then $K$ is a conjugation if and only if there is a complete countable orthonormal basis $(\phi_i)_{i\in I}$ such that, for every $x\in H$,
--
--   $$Kx=\sum_{i\in I}\langle x,\phi_i\rangle\phi_i.$$
--
--   The sum converges in the Hilbert norm; finite and empty bases are permitted. This characterizes conjugations by coordinate conjugation.
--
--   **Formalization Note** Boundedness is the continuity convention used when the source proof applies $K$ to an infinite expansion. Inner products are conjugate-linear in the first variable.
-- source:
--   Operator Isomorphisms on Hilbert Space Tensor Products, arXiv:2010.15901v1, PDF p. 3, Lemma 1.3

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P03

universe u v

open QAlgorithms.Papers.Independent.Claimed50.P34 (HilbertTensor)

/-- Lemma 1.3, PDF p.3, interpreted for bounded anti-linear maps as in its proof.
The series converges in the Hilbert norm, including finite and empty bases. -/
theorem conjugation_basis_formula
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (K : H →L⋆[ℂ] H) :
    IsConjugation K ↔
      ∃ (ι : Type u) (_ : Countable ι) (b : HilbertBasis ι ℂ H),
        ∀ x : H, HasSum (fun i => inner ℂ x (b i) • b i) (K x) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P03

end
