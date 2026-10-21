-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P32_affine_finiteDifference_equivalences
-- name    : QAlgorithms.Papers.Independent.Renew46.P32.affine_finiteDifference_equivalences
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:15:43.838952+00:00
-- url     : https://prove2.me/theorems/d5c7ffcc-555b-4723-98a4-85f7d920a528
-- title:
--   Affine maps and second finite differences
-- statement:
--   Let $E,F$ be abelian groups and $f:E\to F$ a map. Write $\Delta_v f(x)=f(x+v)-f(x)$. The following five conditions are equivalent:
--
--   1. There are an additive map $a:E\to F$ and $b\in F$ with $f(x)=a(x)+b$.
--   2. $\Delta_u\Delta_v f(x)=0$ for every $u,v,x\in E$.
--   3. $\Delta_u\Delta_v f(0)=0$ for every $u,v\in E$.
--   4. For each $x\in E$, the map $v\mapsto\Delta_vf(x)$ is additive.
--   5. The map $v\mapsto\Delta_vf(0)$ is additive.
--
--   The central finite-difference condition is
--   $$\Delta_u\Delta_v f(x)=f(x+u+v)-f(x+u)-f(x+v)+f(x)=0.$$
--
--   This characterizes affine maps without a topology or scalar field.
-- source:
--   Differential Calculus, Manifolds and Lie Groups over Arbitrary Infinite Fields, arXiv:math/0303300v1, PDF p. 64, Lemma A.2

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P32

namespace QAlgorithms.Papers.Independent.Renew46.P32

open Set Filter Topology

universe u v

section AlgebraicDefinitions

variable {K : Type u} [CommRing K]

variable {E : Type u} [AddCommGroup E] [Module K E]

variable {F : Type u} [AddCommGroup F] [Module K F]

/-- Lemma A.2, PDF pp. 64--65: all five affine/additive conditions. -/
theorem affine_finiteDifference_equivalences
    {A : Type u} [AddCommGroup A] {B : Type u} [AddCommGroup B]
    (f : A → B) :
    List.TFAE [
      (∃ a : A →+ B, ∃ b : B, ∀ x, f x = a x + b),
      (∀ x : A, ∀ h : Fin 2 → A, linearization f x 2 h = 0),
      (∀ h : Fin 2 → A, linearization f 0 2 h = 0),
      (∀ x u v : A, f (x + (u + v)) - f x =
        (f (x + u) - f x) + (f (x + v) - f x)),
      (∀ u v : A, f (u + v) - f 0 = (f u - f 0) + (f v - f 0))
    ] := by sorry

end AlgebraicDefinitions

end QAlgorithms.Papers.Independent.Renew46.P32
