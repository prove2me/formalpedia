-- Prove2me | Theorems.Thm_PredAdvice_lemma_3_2
-- name    : PredAdvice.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:34:53.714443+00:00
-- url     : https://prove2.me/theorems/ad4d0a9e-3800-4bcb-b45a-fa1cc6723796
-- title:
--   Lemma 3.2 — covering large pairs by a sample $S$ and sets $Q_u$
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $G=(V,E)$ be a directed unweighted graph with $|V|=n$ and let $2\le D\le n$. There are a set $S\subseteq V$ and sets $Q_u\subseteq V$ ($u\in V$) such that
--
--   1. $|S|\le C\,n\log_2 D/D$,
--   2. $\sum_{u\in V}|Q_u|\le n^2/D$,
--   3. for every large pair $(u,v)$, $S\cap H_{u,v}\ne\emptyset$ or $v\in Q_u$,
--   4. $v\in Q_u$ if and only if $(u,v)$ is large and $S\cap H_{u,v}=\emptyset$.
--
--   The sample $S$ gives two-hop covers through $S$ for most large pairs; the pairs it misses are recorded in the sets $Q_u$, which Lemma 4.3 covers by extending trees.
--
--   Differences from the source:
--   - generalization: clauses 1–3 → clauses 1–3 and the identity v ∈ Q_u ⇔ (u, v) large and S ∩ H_{u,v} = ∅; reason: this is the definition of Q_u in the proof, used in §4 (p.20); dropping clause 4 gives the printed lemma
--   - encoding: H_{u,v} for reachable pairs → H_{u,v} empty for unreachable pairs; large pairs are reachable; reason: no instance changes
--   - generalization: a directed unweighted graph (simple, p.6) → Mathlib's Digraph on a finite vertex type, which may have loops; reason: loops never lie on shortest walks and change no distance; loopless digraphs on n vertices are the special case
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), Lemma 3.2, p.11

import Mathlib
import Definitions.Def_PredAdvice_H

set_option autoImplicit false

namespace PredAdvice

/-- **Lemma 3.2** (covering large pairs; Kopelowitz, Korin, Roditty, *Using Small Advice to Compress the Predecessor Matrix*, STOC 2027 submission (manuscript sha256 0ae8a68d…), §3.1, p.11). Let `G = (V, E)` be a directed
unweighted graph with `|V| = n` and let `2 ≤ D ≤ n`. There are a set `S ⊆ V` and sets `Q_u ⊆ V`
such that

1. `|S| = O(n log D / D)`,
2. `∑_u |Q_u| ≤ n²/D`,
3. for any large pair `(u, v)`, either `S ∩ H_{u,v} ≠ ∅` or `v ∈ Q_u`,

and, as in the proof, `Q_u = {v | (u, v) is large and S ∩ H_{u,v} = ∅}`.

**Formalization Note** The `O(·)` constant `C` is absolute: it is chosen before the vertex type,
the graph and `D`. The last clause is the definition of `Q_u` in the proof ("define
`Q_u := {v | (u, v) is large and missed}`"), which §4 uses (p.20: "By definition of the `Q_u` sets,
the sets `P_S` and `P_Q` partition all large pairs"); it implies clause 3. -/
theorem lemma_3_2 :
    ∃ C : ℝ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : Digraph V) (D : ℕ),
      2 ≤ D → D ≤ Fintype.card V →
      ∃ (S : Finset V) (Q : V → Finset V),
        (S.card : ℝ) ≤ C * ((Fintype.card V : ℝ) * Real.logb 2 D / D) ∧
        ((∑ u, (Q u).card : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / D ∧
        (∀ u v : V, IsLarge G D u v → (S ∩ H G u v).Nonempty ∨ v ∈ Q u) ∧
        (∀ u v : V, v ∈ Q u ↔ IsLarge G D u v ∧ Disjoint S (H G u v)) := by sorry

end PredAdvice
