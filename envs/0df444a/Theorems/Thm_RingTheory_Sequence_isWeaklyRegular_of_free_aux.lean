-- Prove2me | Theorems.Thm_RingTheory_Sequence_isWeaklyRegular_of_free_aux
-- name    : RingTheory.Sequence.isWeaklyRegular_of_free_aux
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/801db96f-af85-57d0-a41c-79e3060585f2
-- title:
--   Weak regularity on a nonzero free module equals weak regularity on R
-- statement:
--   Let $R$ be a commutative ring in universe $u$ and let $M$ be an additive commutative group, in universe $\max(u,v)$, equipped with an $R$-module structure that is free and such that $M$ is nontrivial, i.e. $M \neq 0$. Let $s$ be a list of elements of $R$. The assertion is that $s$ is a weakly regular sequence on $M$ if and only if $s$ is a weakly regular sequence on $R$ regarded as a module over itself; that is, writing $s = (x_1,\dots,x_n)$, the element $x_i$ acts injectively on $M/(x_1,\dots,x_{i-1})M$ for every $i$ precisely when $x_i$ acts injectively on $R/(x_1,\dots,x_{i-1})$ for every $i$. No assumption is made that the list is nonempty, that $R$ is Noetherian, or that $M$ is of finite rank. The universes are constrained: $M$ must live in $\max(u,v)$ with $R$ in $u$, which is the form in which the statement can be proved by an induction that changes the base ring; the version without this restriction is [`RingTheory.Sequence.isWeaklyRegular_of_free`](thm.html#RingTheory.Sequence.isWeaklyRegular_of_free).
--
--   This is the standard fact that weak regularity of a sequence of ring elements is insensitive to replacing the ring by a nonzero free module over it, so that in particular such a module has the same depth as the ring; it is the universe-restricted core from which the general statement [`RingTheory.Sequence.isWeaklyRegular_of_free`](thm.html#RingTheory.Sequence.isWeaklyRegular_of_free) is deduced. In the present development it serves the depth computations for free modules arising over power-series covers in the patching argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RingTheory_Sequence_isWeaklyRegular_of_free_aux.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open scoped Pointwise TensorProduct

theorem RingTheory.Sequence.isWeaklyRegular_of_free_aux {R : Type u} {M : Type max u v} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M] [Nontrivial M] {s : List R} :
    RingTheory.Sequence.IsWeaklyRegular M s ↔ RingTheory.Sequence.IsWeaklyRegular R s := by sorry
