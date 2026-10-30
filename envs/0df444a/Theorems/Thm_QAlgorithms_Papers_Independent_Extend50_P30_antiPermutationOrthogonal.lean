-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_antiPermutationOrthogonal
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.antiPermutationOrthogonal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:18:46.968017+00:00
-- url     : https://prove2.me/theorems/9fc1ea82-9c34-4094-9502-4888040ec8f5
-- title:
--   Binary anti-permutations are stochastic isometries
-- statement:
--   Let $t\equiv2\pmod4$ and let $\pi$ be any permutation of the $t$ coordinates. Over $\mathbb F_2$, its binary complement is a stochastic isometry for the quadratic form valued modulo four. The local dimension is two.
--
--   $$
--   \overline\pi=\mathbf1_t\mathbf1_t^T-\pi\in O_t(2).
--   $$
--
--   This gives the source's binary anti-permutations are stochastic isometries in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 44, lemma-4.30

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.44, Lemma 4.30: the anti-permutation construction is binary. -/
theorem antiPermutationOrthogonal (t : ℕ) (ht : t % 4 = 2) (p : Equiv.Perm (Fin t)) :
    IsStochasticOrthogonal (antiPermutation p) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
