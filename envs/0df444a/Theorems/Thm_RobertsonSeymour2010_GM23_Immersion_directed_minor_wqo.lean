-- Prove2me | Theorems.Thm_RobertsonSeymour2010_GM23_Immersion_directed_minor_wqo
-- name    : RobertsonSeymour2010.GM23.Immersion.directed_minor_wqo
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:12:28.299546+00:00
-- url     : https://prove2.me/theorems/789d908e-24cb-4c77-a7b5-a107fe824c4d
-- title:
--   1.7 — labelled directed graphs are well-quasi-ordered by (labelled, directed) minors
-- statement:
--   Let $\Omega$ be a well-quasi-order. For $i\ge1$ let $G_i$ be a finite directed graph (loops and parallel edges allowed) and $\phi_i:V(G_i)\cup E(G_i)\to\Omega$ a labelling of its vertices and edges. Then there exist $j>i\ge1$ and a map $\eta$ on $V(G_i)\cup E(G_i)$ such that:
--
--   1. for each $v\in V(G_i)$, $\eta(v)$ is a connected subgraph of $G_j$ and some $w\in V(\eta(v))$ has $\phi_i(v)\le\phi_j(w)$; and $\eta(v)$, $\eta(v')$ have no common vertex for distinct $v,v'$;
--   2. for each $e\in E(G_i)$, $\eta(e)$ is an edge of $G_j$, a loop if and only if $e$ is a loop, with $\phi_i(e)\le\phi_j(\eta(e))$; and $\eta(e)\ne\eta(e')$ for distinct $e,e'$;
--   3. for each $e\in E(G_i)$ with head $u$ and tail $v$, $\eta(e)$ has head in $V(\eta(u))$ and tail in $V(\eta(v))$, and $\eta(e)$ is not an edge of $\eta(u)$ or of $\eta(v)$.
--
--   This is a labelled, directed version of Wagner's conjecture, derived in the paper from 1.6.
--
--   **Formalization Note.** The labelling is `φ i : V i ⊕ E i → Ω` (vertices and edges are disjoint). $\eta$ is a pair of maps: `ηv` sending vertices of $G_i$ to subgraphs of $G_j$ and `ηe` sending edges to edges. "$\eta(v)\cap\eta(v')$ is null" is read as disjointness of the vertex sets. Connectivity is in the underlying undirected sense and includes non-emptiness. The sequence is indexed from $0$.
-- source:
--   Robertson, Seymour, Graph Minors XXIII. Nash-Williams' immersion conjecture (authors' manuscript, rev. Apr. 18, 2011), 1.7, p. 4

import Mathlib
import Definitions.Def_RobertsonSeymour2010_GM23_Immersion_DirGraphs

namespace RobertsonSeymour2010.GM23.Immersion

theorem directed_minor_wqo (Ω : Type) [Preorder Ω]
    (hΩ : WellQuasiOrdered (α := Ω) (· ≤ ·))
    (V E : ℕ → Type) [∀ i, Fintype (V i)] [∀ i, Fintype (E i)]
    (G : ∀ i, DirGraph (V i) (E i)) (φ : ∀ i, V i ⊕ E i → Ω) :
    ∃ i j : ℕ, i < j ∧ ∃ (ηv : V i → (G j).Subgraph) (ηe : E i → E j),
      -- first bullet
      (∀ v : V i, (ηv v).Connected ∧ ∃ w ∈ (ηv v).verts, φ i (Sum.inl v) ≤ φ j (Sum.inl w)) ∧
      (∀ v v' : V i, v ≠ v' → Disjoint (ηv v).verts (ηv v').verts) ∧
      -- second bullet
      (∀ e : E i, ((G j).IsLoop (ηe e) ↔ (G i).IsLoop e) ∧ φ i (Sum.inr e) ≤ φ j (Sum.inr (ηe e))) ∧
      Function.Injective ηe ∧
      -- third bullet
      (∀ e : E i,
        (G j).head (ηe e) ∈ (ηv ((G i).head e)).verts ∧
        (G j).tail (ηe e) ∈ (ηv ((G i).tail e)).verts ∧
        ηe e ∉ (ηv ((G i).head e)).edges ∧ ηe e ∉ (ηv ((G i).tail e)).edges) := by sorry

end RobertsonSeymour2010.GM23.Immersion
