-- Prove2me | Theorems.Thm_Subalgebra_fg_restrictScalars_and_le_of_fg
-- name    : Subalgebra.fg_restrictScalars_and_le_of_fg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/82a2d955-d674-5111-89f9-90a63704c3a7
-- title:
--   Transitivity of finite generation for subalgebras
-- statement:
--   Let $A_0$ and $A$ be commutative rings in a common universe, with $A$ an $A_0$-algebra. Let $T$ be an $A_0$-subalgebra of $A$ which is finitely generated, in the sense of `Subalgebra.FG`: there is a finite subset of $A$ whose generated $A_0$-subalgebra is $T$. Let $T'$ be a subalgebra of $A$ over the ring $T$ (the coercion of $T$ to a type, with its induced algebra structure on $A$), again assumed finitely generated over $T$. The conclusion is a conjunction: first, the restriction of scalars $T'.\mathrm{restrictScalars}\,A_0$ — the same subset of $A$ regarded as an $A_0$-subalgebra — is finitely generated as an $A_0$-subalgebra of $A$; second, the underlying set of $T$ is contained in the underlying set of $T'.\mathrm{restrictScalars}\,A_0$, i.e. $T \subseteq T'$ as subsets of $A$. Thus a finitely generated $T$-subalgebra of $A$ is, viewed over $A_0$, a finitely generated $A_0$-subalgebra of $A$ containing $T$.
--
--   This is the standard transitivity of finite generation for algebras, packaged together with the inclusion $T \subseteq T'$ so that a two-step construction of subalgebras can be collapsed into a single finitely generated $A_0$-subalgebra without nested subtypes. It is used in the approximation of schemes and of pullback diagrams by finitely generated subalgebras, in [`AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation`](thm.html#AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation) and [`AlgebraicGeometry.exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation`](thm.html#AlgebraicGeometry.exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Subalgebra_fg_restrictScalars_and_le_of_fg.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Subalgebra.fg_restrictScalars_and_le_of_fg
    {A₀ A : Type u} [CommRing A₀] [CommRing A] [Algebra A₀ A]
    (T : Subalgebra A₀ A) (hT : T.FG) (T' : Subalgebra ↥T A) (hT' : T'.FG) :
    (T'.restrictScalars A₀).FG ∧ (T : Set A) ⊆ (T'.restrictScalars A₀ : Set A) := by sorry
