-- Prove2me | Theorems.Thm_TensorProduct_eq_zero_of_forall_lTensor_eq_zero_of_field
-- name    : TensorProduct.eq_zero_of_forall_lTensor_eq_zero_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/45ade77c-c213-5fc0-b43e-075006e9c8dd
-- title:
--   Dévissage: field case implies finitely generated case
-- statement:
--   Let $A$ be a commutative Noetherian ring, let $B$ be a flat $A$-module, let $J$ be an index type and let $(N_j)_{j\in J}$ be a family of flat $A$-modules, all equipped with the usual additive-group and module structures. Given a family of $A$-linear maps $f_j\colon B\to N_j$, consider for an $A$-module $M$ the condition that an element $g\in M\otimes_A B$ satisfy $(\mathrm{id}_M\otimes f_j)(g)=0$ in $M\otimes_A N_j$ for every $j$. The hypothesis `hK` is that for every field $K$ (in the same universe as $A$) carrying an $A$-algebra structure, every $g\in K\otimes_A B$ with $(\mathrm{id}_K\otimes f_j)(g)=0$ for all $j$ is already zero. The conclusion: for every finitely generated $A$-module $M$ (again in the universe of $A$) and every $g\in M\otimes_A B$ such that $(\mathrm{id}_M\otimes f_j)(g)=0$ for all $j$, one has $g=0$. Note the universe constraints: $B$ and the $N_j$ lie in one universe, $A$, the test fields $K$ and the module $M$ in another.
--
--   This is the dévissage step that lets a vanishing criterion verified over all field-valued $A$-algebras be upgraded to arbitrary finitely generated coefficient modules; it is the commutative algebra underlying Katz's passage from field coefficients to general coefficients in the $q$-expansion principle. It is used in the treatment of level-$p$ Katz forms, in the results asserting that a form whose values at the cusps vanish is itself zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TensorProduct_eq_zero_of_forall_lTensor_eq_zero_of_field.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open scoped TensorProduct

theorem TensorProduct.eq_zero_of_forall_lTensor_eq_zero_of_field
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {B : Type v} [AddCommGroup B] [Module A B] [Module.Flat A B]
    {J : Type w} {N : J → Type v} [∀ j, AddCommGroup (N j)] [∀ j, Module A (N j)]
    [∀ j, Module.Flat A (N j)] (f : ∀ j, B →ₗ[A] N j)
    (hK : ∀ (K : Type u) [Field K] [Algebra A K] (g : K ⊗[A] B),
      (∀ j, LinearMap.lTensor K (f j) g = 0) → g = 0)
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (g : M ⊗[A] B) (hg : ∀ j, LinearMap.lTensor M (f j) g = 0) : g = 0 := by sorry
