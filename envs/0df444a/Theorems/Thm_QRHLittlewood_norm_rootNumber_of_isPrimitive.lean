-- Prove2me | Theorems.Thm_QRHLittlewood_norm_rootNumber_of_isPrimitive
-- name    : QRHLittlewood.norm_rootNumber_of_isPrimitive
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T15:43:55.458284+00:00
-- url     : https://prove2.me/theorems/e93a7eb7-a2c8-40d7-8ded-21d38ca6a6c5
-- title:
--   The root number of a primitive Dirichlet character has modulus $1$
-- statement:
--   Let $\chi$ be a primitive Dirichlet character modulo $N\ge1$, and let $\varepsilon(\chi)=\tau(\chi)/(i^{a}\sqrt N)$ be the root number in the functional equation of its completed $L$-function, where $a=0$ for even $\chi$ and $a=1$ for odd $\chi$. Then
--
--   $$|\varepsilon(\chi)|=1.$$
--
--   **Formalization Note** The root number is Mathlib's `DirichletCharacter.rootNumber`, which appears in `DirichletCharacter.IsPrimitive.completedLFunction_one_sub`.
-- source:
--   H. Davenport, Multiplicative Number Theory, 3rd ed., Springer GTM 74, Chapter 9.

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

open Complex

namespace QRHLittlewood

theorem norm_rootNumber_of_isPrimitive {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) : ‖DirichletCharacter.rootNumber χ‖ = 1 := by sorry

end QRHLittlewood
