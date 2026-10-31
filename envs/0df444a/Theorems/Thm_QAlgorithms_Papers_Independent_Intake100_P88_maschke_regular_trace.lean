-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P88_maschke_regular_trace
-- name    : QAlgorithms.Papers.Independent.Intake100.P88.maschke_regular_trace
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:44:22.146211+00:00
-- url     : https://prove2.me/theorems/4361b0d6-2d0c-4c31-99da-7b2d383ef36a
-- title:
--   Theorem 5.8: Maschke criterion from regular trace
-- statement:
--   Let $A$ be a finite-dimensional unital algebra over a field $F$. Let $t(a)$ be the ordinary trace of left multiplication by $a$ on $A$. Suppose $t$ is nondegenerate, meaning that each $b\ne0$ has an $a$ with $t(ba)\ne0$. Then every finite-dimensional unital representation $M$ of $A$ is completely decomposable:
--
--   $$M\text{ is a semisimple }A\text{-module}.$$
--
--   The finite-dimensional representation convention is the one used by the source's induction on dimension. No characteristic restriction is required when nondegeneracy of the actual regular trace is a hypothesis.
-- source:
--   Partition Algebras, arXiv:math/0401314v2, PDF p. 43, Theorem 5.8: Maschke criterion from regular trace

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P88

attribute [local instance] Classical.propDecidable

open scoped BigOperators Matrix

open QAlgorithms.Papers.Independent.Information100.P65 (hookLength)

open QAlgorithms.Papers.Independent.Renew46.P30 (TensorIndex)

universe u v w x y

/-- Nondegenerate regular trace implies complete decomposability, PDF pp.43--44, Theorem 5.8.
The finite-dimensional representation convention is the one used in the source's induction. -/
theorem maschke_regular_trace (F A M : Type*) [Field F] [Ring A] [Algebra F A]
    [FiniteDimensional F A] [AddCommGroup M] [Module F M] [Module A M]
    [IsScalarTower F A M] [FiniteDimensional F M]
    (_hnd : TraceNondegenerate (regularTrace (F := F) (A := A))) :
    IsSemisimpleModule A M := by sorry

end QAlgorithms.Papers.Independent.Intake100.P88

end
