-- Prove2me | Theorems.Thm_Rep_nonempty_splitting_of_isZero_H1_ihom
-- name    : Rep.nonempty_splitting_of_isZero_H1_ihom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/472d6934-19ea-5792-8d6e-09fb913b85c0
-- title:
--   Short exact sequences of representations split when H¹ of the internal Hom vanishes
-- statement:
--   Let $k$ be a commutative ring and $G$ a group (both in the same universe), and let $X$ be a short complex $X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3$ in the category $\mathrm{Rep}\,k\,G$ of $k$-linear representations of $G$. Assume that $X$ is short exact in Mathlib's sense, i.e. $f$ is a monomorphism, $g$ is an epimorphism and the complex is exact, that the underlying $k$-module of $X_3$ is free, and that the degree-one group cohomology $H^1\bigl(G, (\mathrm{ihom}\,X_3)(X_1)\bigr)$ is a zero object, where $(\mathrm{ihom}\,X_3)(X_1)$ is the internal Hom of the monoidal closed category $\mathrm{Rep}\,k\,G$, namely $\operatorname{Hom}_k(X_3, X_1)$ with the conjugation action $(g\cdot t) = \rho_{X_1}(g)\circ t\circ\rho_{X_3}(g^{-1})$. Then the type of splittings of $X$ is nonempty: there are morphisms of representations $r : X_2 \to X_1$ and $s : X_3 \to X_2$ with $f$ followed by $r$ the identity of $X_1$, $s$ followed by $g$ the identity of $X_3$, and the sum of $r$ followed by $f$ and of $g$ followed by $s$ the identity of $X_2$.
--
--   This is the standard criterion identifying the obstruction to splitting a short exact sequence of $G$-representations, $k$-linearly split because the quotient is free, with a class in $H^1(G,\operatorname{Hom}_k(X_3,X_1))$. It is used in the construction of equivariant retractions, being cited by [`Rep.exists_retract_free_of_forall_isZero`](thm.html#Rep.exists_retract_free_of_forall_isZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_nonempty_splitting_of_isZero_H1_ihom.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory

theorem Rep.nonempty_splitting_of_isZero_H1_ihom {k G : Type u} [CommRing k] [Group G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) [Module.Free k X.X₃]
    (h : CategoryTheory.Limits.IsZero (groupCohomology ((ihom X.X₃).obj X.X₁) 1)) :
    Nonempty X.Splitting := by sorry
