-- Prove2me | Theorems.Thm_QRHLittlewood_normSq_gaussSum_of_isPrimitive
-- name    : QRHLittlewood.normSq_gaussSum_of_isPrimitive
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T15:43:54.573819+00:00
-- url     : https://prove2.me/theorems/f6386f48-0194-43b1-a05f-afec0a51bcdb
-- title:
--   $|\tau(\chi)|^2=N$ for primitive Dirichlet characters
-- statement:
--   Let $\chi$ be a primitive Dirichlet character modulo $N\ge1$ and let
--   $$\tau(\chi)=\sum_{a\in\mathbb Z/N\mathbb Z}\chi(a)\,e^{2\pi i a/N}$$
--   be its Gauss sum with respect to the standard additive character. Then
--
--   $$|\tau(\chi)|^2=N.$$
--
--   This holds for every modulus, prime or composite. It gives $|\tau(\chi)|=\sqrt N$ and hence the unit modulus of the root number in the functional equation of $L(s,\chi)$.
--
--   **Formalization Note** The Gauss sum is Mathlib's `gaussSum χ ZMod.stdAddChar` and primitivity is `DirichletCharacter.IsPrimitive`.
-- source:
--   H. Davenport, Multiplicative Number Theory, 3rd ed., Springer GTM 74, Chapter 9 (Gauss sums for primitive characters).

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

open Complex

namespace QRHLittlewood

theorem normSq_gaussSum_of_isPrimitive {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) : Complex.normSq (gaussSum χ ZMod.stdAddChar) = N := by sorry

end QRHLittlewood
