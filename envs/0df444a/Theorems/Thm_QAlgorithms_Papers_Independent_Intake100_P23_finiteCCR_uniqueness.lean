-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P23_finiteCCR_uniqueness
-- name    : QAlgorithms.Papers.Independent.Intake100.P23.finiteCCR_uniqueness
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:42:12.97684+00:00
-- url     : https://prove2.me/theorems/3ec4631a-9fa2-4819-8790-08d4775d3663
-- title:
--   Finite-dimensional regular irreducible CCR uniqueness
-- statement:
--   Let $(Y,\omega)$ be a finite-dimensional real symplectic vector space; thus $\omega$ is antisymmetric and nondegenerate. Let $W_j:Y\to\mathcal U(H_j)$, $j=1,2$, be regular irreducible Weyl representations on nonzero complex Hilbert spaces. Then they are unitarily equivalent:
--   $$\exists U:H_1\overset{\sim}{\longrightarrow}H_2\text{ unitary},\qquad UW_1(y)=W_2(y)U\quad(y\in Y).$$
--   The representation spaces may differ and need not be assumed separable. This identifies all irreducible regular representations of a finite symplectic space.
-- source:
--   Introduction to representations of the canonical commutation and anticommutation relations, arXiv:math-ph/0511030v2, PDF p. 12, Corollary 1: equivalence of finite-dimensional irreducible regular CCR

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P23

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P23

open QAlgorithms.Papers.Independent.Renew46.P03 (tensorVector)

variable {Y : Type*} [AddCommGroup Y] [Module ℝ Y]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF p.12, Corollary 1: regular irreducible finite-dimensional CCR uniqueness. -/
theorem finiteCCR_uniqueness [FiniteDimensional ℝ Y]
    {H2 : Type*} [NormedAddCommGroup H2] [InnerProductSpace ℂ H2] [CompleteSpace H2]
    [Nontrivial H] [Nontrivial H2]
    (omega : Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hanti : Antisymmetric omega)
    (hnd : FormNondegenerate omega)
    (W1 : Y → H →L[ℂ] H) (W2 : Y → H2 →L[ℂ] H2)
    (h1 : IsCCR omega W1) (h2 : IsCCR omega W2)
    (hr1 : WeylRegular W1) (hr2 : WeylRegular W2)
    (hi1 : HilbertIrreducible W1) (hi2 : HilbertIrreducible W2) :
    EquivalentCCR W1 W2 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P23

end
