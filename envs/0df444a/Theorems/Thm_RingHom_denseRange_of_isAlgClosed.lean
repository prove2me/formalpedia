-- Prove2me | Theorems.Thm_RingHom_denseRange_of_isAlgClosed
-- name    : RingHom.denseRange_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/22467ca1-268a-5f65-9e51-908cb199e712
-- title:
--   Image of an algebraically closed field is dense in ℂ
-- statement:
--   Let $F$ be a field which is algebraically closed and of characteristic zero, and let $\sigma \colon F \to \mathbb{C}$ be a ring homomorphism. Then $\sigma$ has dense range, i.e. the image $\sigma(F)$ is a dense subset of $\mathbb{C}$ for the usual topology, so that its closure is all of $\mathbb{C}$. No further hypotheses are imposed: $\sigma$ is not assumed continuous (indeed $F$ carries no topology), nor injective, nor is $F$ assumed to be of finite transcendence degree or to be an algebraic closure of $\mathbb{Q}$; the conclusion is the topological statement `DenseRange σ` about the set-theoretic image of the ring homomorphism.
--
--   This is the elementary observation that any ring homomorphism to $\mathbb{C}$ from an algebraically closed field of characteristic zero has image containing a copy of $\mathbb{Q}(i)$, hence dense image; in particular the algebraic numbers are dense in $\mathbb{C}$ under any embedding. It is used by [`RingHom.exists_mem_forall_mem_range_of_isOpen`](thm.html#RingHom.exists_mem_forall_mem_range_of_isOpen) to produce points of the image inside prescribed non-empty open subsets, i.e. to choose algebraic witnesses for open conditions on complex parameters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RingHom_denseRange_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem RingHom.denseRange_of_isAlgClosed {F : Type*} [Field F] [IsAlgClosed F] [CharZero F] (σ : F →+* ℂ) :
    DenseRange σ := by sorry
