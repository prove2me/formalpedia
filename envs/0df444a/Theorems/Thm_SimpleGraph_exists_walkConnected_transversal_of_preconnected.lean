-- Prove2me | Theorems.Thm_SimpleGraph_exists_walkConnected_transversal_of_preconnected
-- name    : SimpleGraph.exists_walkConnected_transversal_of_preconnected
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/3a345bde-711e-5ffe-854b-2b82dd8748d2
-- title:
--   Walk-connected orbit transversal in a preconnected graph
-- statement:
--   Let $V$ be a type carrying a simple graph $T$, and let $\Gamma$ be a group acting on $V$. Assume that the action preserves adjacency: for every $\gamma \in \Gamma$ and all $v, w \in V$, if $v$ and $w$ are adjacent in $T$ then so are $\gamma \cdot v$ and $\gamma \cdot w$. Assume further that $T$ is preconnected, i.e. any two vertices are joined by a walk, and fix a base vertex $v_0 \in V$. The conclusion is the existence of a set $D \subseteq V$ with the following four properties: $v_0 \in D$; for all $v, w \in D$ there is a walk $p$ in $T$ from $v$ to $w$ all of whose support lies in $D$; for all $v, w \in D$, if $v$ lies in the $\Gamma$-orbit of $w$ then $v = w$; and for every $u \in V$ there is some $v \in D$ lying in the $\Gamma$-orbit of $u$. Thus $D$ is walk-connected inside $T$, contains $v_0$, and meets every $\Gamma$-orbit in exactly one point. No finiteness, freeness or stabiliser hypothesis is imposed.
--
--   This is the vertex-set form of Serre's tree of representatives (fundamental domain) for a group acting on a connected graph, as in §I.3 of Serre's Trees. It is used in the present development in the treatment of free products, supporting the Kurosh/Nielsen–Schreier style statements [`Monoid.CoprodI.nonempty_freeGroupBasis_fin_kuroshRank`](thm.html#Monoid.CoprodI.nonempty_freeGroupBasis_fin_kuroshRank) and [`Monoid.CoprodI.finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one`](thm.html#Monoid.CoprodI.finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_SimpleGraph_exists_walkConnected_transversal_of_preconnected.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem SimpleGraph.exists_walkConnected_transversal_of_preconnected {V : Type*} {T : SimpleGraph V} {Γ : Type*} [Group Γ] [MulAction Γ V]
    (hsmul : ∀ (γ : Γ) {v w : V}, T.Adj v w → T.Adj (γ • v) (γ • w))
    (hpre : T.Preconnected) (v₀ : V) :
    ∃ D : Set V, v₀ ∈ D ∧
      (∀ v ∈ D, ∀ w ∈ D, ∃ p : T.Walk v w, ∀ x ∈ p.support, x ∈ D) ∧
      (∀ v ∈ D, ∀ w ∈ D, v ∈ MulAction.orbit Γ w → v = w) ∧
      (∀ u : V, ∃ v ∈ D, v ∈ MulAction.orbit Γ u) := by sorry
