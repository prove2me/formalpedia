-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P88_simple_hom_zero
-- name    : QAlgorithms.Papers.Independent.Intake100.P88.simple_hom_zero
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:42:46.855771+00:00
-- url     : https://prove2.me/theorems/b9d0faf0-7cb1-45e7-9790-25118a41bc70
-- title:
--   Theorem 5.3(2): Hom between distinct simple modules
-- statement:
--   Let $A$ be a finite-dimensional unital algebra over an algebraically closed field $F$. Let $M,N$ be simple unital $A$-modules with compatible $F$-vector-space structures, and assume they are not isomorphic as $A$-modules. Then
--
--   $$\operatorname{Hom}_A(M,N)=0.$$
--
--   Every $A$-linear map is therefore the zero map. Nonisomorphism concerns modules rather than their names; this is the off-diagonal part of Schur's lemma.
-- source:
--   Partition Algebras, arXiv:math/0401314v2, PDF p. 41, Theorem 5.3(2): Hom between distinct simple modules

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P88

attribute [local instance] Classical.propDecidable

open scoped BigOperators Matrix

open QAlgorithms.Papers.Independent.Information100.P65 (hookLength)

open QAlgorithms.Papers.Independent.Renew46.P30 (TensorIndex)

universe u v w x y

/-- Hom between nonisomorphic simple modules vanishes, PDF pp.40--41, Theorem 5.3(2). -/
theorem simple_hom_zero (F A M N : Type*) [Field F] [IsAlgClosed F]
    [Ring A] [Algebra F A] [FiniteDimensional F A]
    [AddCommGroup M] [AddCommGroup N] [Module F M] [Module F N]
    [Module A M] [Module A N] [IsScalarTower F A M] [IsScalarTower F A N]
    [IsSimpleModule A M] [IsSimpleModule A N] (_hne : ¬ Nonempty (M ≃ₗ[A] N)) :
    ∀ f : M →ₗ[A] N, f = 0 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P88

end
