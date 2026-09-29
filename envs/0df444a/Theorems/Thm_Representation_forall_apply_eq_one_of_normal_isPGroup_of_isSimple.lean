-- Prove2me | Theorems.Thm_Representation_forall_apply_eq_one_of_normal_isPGroup_of_isSimple
-- name    : Representation.forall_apply_eq_one_of_normal_isPGroup_of_isSimple
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/11734163-82d5-5b1b-a85b-3db6e6e54091
-- title:
--   Normal p-subgroups act trivially on simple mod-p representations
-- statement:
--   Let $p$ be a prime, $k$ a finite field of characteristic $p$, $\Delta$ a finite group, and $V$ a finite-dimensional $k$-vector space with $\operatorname{finrank}_k V \neq 0$. Let $\rho : \Delta \to \operatorname{End}_k(V)$ be a $k$-linear representation of $\Delta$ on $V$, assumed simple in the following explicit sense: for every $k$-submodule $W \subseteq V$ such that $\rho(d)v \in W$ for all $d \in \Delta$ and all $v \in W$, one has $W = \bot$ or $W = \top$. Let $P$ be a normal subgroup of $\Delta$ which is a $p$-group in the sense of the predicate `IsPGroup p P`, i.e. every element of $P$ has order a power of $p$. The conclusion is that $\rho$ is trivial on $P$: for every $x \in P$ the endomorphism $\rho(x)$ equals the identity map of $V$. Note that simplicity is phrased as the stability condition above rather than through a simple-module typeclass, and that nonvanishing of $V$ is expressed by $\operatorname{finrank}_k V \neq 0$.
--
--   This is the standard fact that the subgroup $O_p$ of the image of a simple representation in characteristic $p$ is trivial, in the form used to show that a normal $p$-subgroup (for instance wild inertia) acts trivially on every simple mod-$p$ representation. It is used by [`ExtCitation.tame_or_descent_of_isSimple`](thm.html#ExtCitation.tame_or_descent_of_isSimple) and by [`HopfAlgebra.exists_field_lineAction_of_finite_flat_of_inertiaSimple_step`](thm.html#HopfAlgebra.exists_field_lineAction_of_finite_flat_of_inertiaSimple_step).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_forall_apply_eq_one_of_normal_isPGroup_of_isSimple.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open Module

theorem Representation.forall_apply_eq_one_of_normal_isPGroup_of_isSimple
    {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] [Finite k] [CharP k p]
    {Δ : Type*} [Group Δ] [Finite Δ] {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k Δ V) (hV : Module.finrank k V ≠ 0)
    (hsimple : ∀ W : Submodule k V, (∀ (d : Δ) (v : V), v ∈ W → ρ d v ∈ W) → W = ⊥ ∨ W = ⊤)
    (P : Subgroup Δ) [P.Normal] (hP : IsPGroup p P) :
    ∀ x ∈ P, ρ x = 1 := by sorry
