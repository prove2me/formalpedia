-- Prove2me | Theorems.Thm_RobertsonSeymour2010_GM23_Immersion_collapse_wqo_ordered_ends
-- name    : RobertsonSeymour2010.GM23.Immersion.collapse_wqo_ordered_ends
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:12:31.869201+00:00
-- url     : https://prove2.me/theorems/59acee88-39ef-46f7-8102-80e316482c50
-- title:
--   1.6 — labelled hypergraphs with ordered bounded edges are well-quasi-ordered by collapse
-- statement:
--   Let $\Omega$ be a well-quasi-order and $k\ge0$ an integer. For $i=1,2,\dots$ let $G_i$ be a finite hypergraph, $\phi_i:E(G_i)\to\Omega$ a labelling of its edges, and $M_i\subseteq E(G_i)$ a set of edges with $|V(e)|\le k$ for all $e\in M_i$. For each $e\in M_i$ let $\mu_i(e)=(v_1,\dots,v_m)$ be a sequence of pairwise distinct vertices with $\{v_1,\dots,v_m\}=V(e)$. Then there exist $j>i\ge1$ and a collapse $\eta$ of $G_j$ to $G_i$ such that for every $e\in E(G_i)$:
--
--   1. $\phi_i(e)\le\phi_j(\eta(e))$;
--   2. $\eta(e)\in M_j$ if and only if $e\in M_i$, and in that case $|V(\eta(e))|=|V(e)|$;
--   3. if $e\in M_i$, $\mu_i(e)=(v_1,\dots,v_m)$ and $\mu_j(\eta(e))=(u_1,\dots,u_m)$, then
--   $$u_h\in V(\eta(v_h))\qquad\text{for }1\le h\le m .$$
--
--   This is the paper's most general result. With $M_i=\emptyset$ it is 1.4; with $M_i=E(G_i)$ and edges of one or two ends it gives a labelled form of Wagner's conjecture (1.7).
--
--   **Formalization Note.** Sequences are indexed from $0$. $\mu_i$ is a function `E i → List (V i)` whose values matter only on $M_i$; the hypotheses require, for $e\in M_i$, that the list has no repetitions and that its entries are exactly the ends of $e$. The third bullet is `List.Forall₂`, which pairs the $h$-th entries of $\mu_j(\eta(e))$ and $\mu_i(e)$ for every $h$ (lists are $0$-based) and includes equality of the lengths. $|V(e)|$ is `Set.ncard` of the end set.
-- source:
--   Robertson, Seymour, Graph Minors XXIII. Nash-Williams' immersion conjecture (authors' manuscript, rev. Apr. 18, 2011), 1.6, p. 3

import Mathlib
import Definitions.Def_RobertsonSeymour2010_GM23_Immersion_Graphs

namespace RobertsonSeymour2010.GM23.Immersion

theorem collapse_wqo_ordered_ends (Ω : Type) [Preorder Ω]
    (hΩ : WellQuasiOrdered (α := Ω) (· ≤ ·)) (k : ℕ)
    (V E : ℕ → Type) [∀ i, Fintype (V i)] [∀ i, Fintype (E i)]
    (G : ∀ i, Hypergraph (V i) (E i)) (φ : ∀ i, E i → Ω) (M : ∀ i, Set (E i))
    (hM : ∀ i, ∀ e ∈ M i, ((G i).endSet e).ncard ≤ k)
    (μ : ∀ i, E i → List (V i))
    (hμ : ∀ i, ∀ e ∈ M i, (μ i e).Nodup ∧ ∀ v, v ∈ μ i e ↔ (G i).inc e v) :
    ∃ i j : ℕ, i < j ∧ ∃ η : Collapse (G j) (G i), ∀ e : E i,
      φ i e ≤ φ j (η.emap e) ∧
      (η.emap e ∈ M j ↔ e ∈ M i) ∧
      (e ∈ M i → ((G j).endSet (η.emap e)).ncard = ((G i).endSet e).ncard) ∧
      (e ∈ M i → List.Forall₂ (fun (u : V j) (v : V i) => u ∈ (η.vmap v).verts)
        (μ j (η.emap e)) (μ i e)) := by sorry

end RobertsonSeymour2010.GM23.Immersion
