-- Prove2me | Theorems.Thm_SemiStreamMWM_lemma_3_3
-- name    : SemiStreamMWM.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:27:17.715218+00:00
-- url     : https://prove2.me/theorems/c80070a0-de19-47f7-a3b0-cab5c0edd391
-- title:
--   Lemma 3.3 — the cut partition has $O(\mu(G)/\delta)$ internal edges
-- statement:
--   Let $0<\delta<1$, $x\in\mathcal P_{G,\delta}$, and let $\mathcal Q$ be the partition of §3.1: the inclusion-maximal members of the family of inclusion-minimal minimum $v$–$r$ cut sides $Q_v$ in $G_{\tilde x,\delta}$. Then the number of internal edges of $\mathcal Q$ (edges with both endpoints in one part) is
--
--   $$O(\mu(G)/\delta),$$
--
--   with an absolute constant, where $\mu(G)$ is the maximum matching cardinality.
--
--   This is property 1 of Lemma 3.1: the internal graph is small enough to be stored and solved exactly.
--
--   Differences from the source:
--   - generalization: δ = t log W ≤ 1/32 (the setting of every application) → every 0 < δ < 1; reason: the bound holds for all such δ (for δ > 1/2 every part is a singleton); it specializes to the paper's δ
--   - generalization: Q_v the (unique) inclusion-minimal minimum cut side → any choice of inclusion-minimal minimum cut sides; reason: uniqueness is not assumed; the statement covers the paper's choice
--   - encoding: O(µ(G)/δ) → A · µ(G)/δ with ∃ A before the vertex type, graph, δ and x; reason: an absolute constant (the proof gives 4)
-- source:
--   J. Chen, Faster Semi-Streaming and Dynamic Approximate Maximum Weight Matchings in General Graphs: A Unified Framework (STOC 2027 submission, preprint, arXiv:2611.02105, sha256 83213124981525da907e0f2f9e1e9da47f70f80b9aa72c30767fb094e3bf6934), Lemma 3.3, p.14 (proof p.15); §3.1 p.14

import Mathlib
import Definitions.Def_SemiStreamMWM_Graph
import Definitions.Def_SemiStreamMWM_CutPartition

open Classical

namespace SemiStreamMWM

/-- J. Chen (STOC 2027 submission, arXiv:2611.02105, sha256 83213124…), Lemma 3.3, p.14 (proof p.15),
for the partition `Q` of §3.1 (p.14).

"The partition Q has O(µ(G)/δ) internal edges."

**Formalization Note.** `Q` consists of the inclusion-maximal members of the family of
inclusion-minimal minimum cut sides `Qf v` (`partsOf Qf`). `µ(G)` is the maximum matching
cardinality. The `O`-constant `A` is absolute: it comes before the vertex type, the graph, `δ`, `x`
and the choice of the sides. The statement is posed for every `0 < δ < 1` (the paper's applications
have `δ ≤ 1/32`). -/
theorem lemma_3_3 : ∃ A : ℝ, ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (δ : ℝ)
    (x : G.edgeSet → ℝ) (Qf : V → Finset V),
    0 < δ → δ < 1 → x ∈ truncPolytope G δ → (∀ v, IsMinimalMinCutSide G δ x v (Qf v)) →
    ((internalEdges G (partsOf Qf)).card : ℝ) ≤ A * mcm G / δ := by sorry

end SemiStreamMWM
