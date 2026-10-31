-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P23_finiteEvenCAR_uniqueness
-- name    : QAlgorithms.Papers.Independent.Intake100.P23.finiteEvenCAR_uniqueness
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:10:50.778878+00:00
-- url     : https://prove2.me/theorems/7dfd7660-34da-4069-a0c6-cc233a618231
-- title:
--   Uniqueness of finite even-dimensional irreducible CAR
-- statement:
--   Let $Y$ be a finite-dimensional real Hilbert space of even dimension. Let $\phi_j:Y\to B(H_j)$ be irreducible CAR representations on nonzero complex Hilbert spaces, with the real-linear self-adjoint factor-2 convention. Then a unitary $U:H_1\to H_2$ exists such that
--   $$U\phi_1(y)=\phi_2(y)U\qquad(y\in Y).$$
--   This is the finite even-dimensional uniqueness theorem; it makes no uniqueness assertion for infinite-dimensional CAR label spaces.
-- source:
--   Introduction to representations of the canonical commutation and anticommutation relations, arXiv:math-ph/0511030v2, PDF p. 17, Corollary 2: equivalence of even-dimensional irreducible CAR

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P23

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P23

open QAlgorithms.Papers.Independent.Renew46.P03 (tensorVector)

variable {Y : Type*} [AddCommGroup Y] [Module ℝ Y]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section CAR

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- PDF p.17, Corollary 2: finite even real dimension, arbitrary nonzero H1,H2. -/
theorem finiteEvenCAR_uniqueness [CompleteSpace E] [FiniteDimensional ℝ E]
    {H2 : Type*} [NormedAddCommGroup H2] [InnerProductSpace ℂ H2] [CompleteSpace H2]
    [Nontrivial H] [Nontrivial H2] (heven : Even (Module.finrank ℝ E))
    (phi1 : E → H →L[ℂ] H) (phi2 : E → H2 →L[ℂ] H2)
    (h1 : IsCAR phi1) (h2 : IsCAR phi2) (hi1 : HilbertIrreducible phi1) (hi2 : HilbertIrreducible phi2) :
    EquivalentCAR phi1 phi2 := by sorry

end CAR

end QAlgorithms.Papers.Independent.Intake100.P23

end
