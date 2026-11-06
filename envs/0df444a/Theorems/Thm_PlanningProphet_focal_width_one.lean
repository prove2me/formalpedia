-- Prove2me | Theorems.Thm_PlanningProphet_focal_width_one
-- name    : PlanningProphet.focal_width_one
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:12:51.700198+00:00
-- url     : https://prove2.me/theorems/778492ba-c3fa-44a1-9d70-9ea433551d64
-- title:
--   §4.1, p.12 — each $G_i$ is a width-1 instance of the model
-- statement:
--   Let $G$ be a DAG covered by the $s,t$-paths $P_1,\dots,P_k$. Suppose every edge has at most $d$ labels, $c_\ell\ge1$, and every labelled edge has a parallel unlabelled edge. Let $G_i$ be the graph of §4.1 built from $P_i$. Then for every $i$:
--
--   1. $G_i$ is acyclic and is covered by a single $s,t$-path, so it has width 1;
--   2. every edge of $G_i$ has at most $d$ labels, every capacity is at least $1$, and every labelled edge of $G_i$ has a parallel unlabelled edge;
--   3. for every edge $e=(u,v)$ of $G$ with $u\in V(P_i)$ and $v\notin V(P_i)$, some node of $V(P_i)$ is reachable from $v$ ("there is always a node $v'$"). The head of the artificial edge $e'$ is a node of $V(P_i)$ reachable from $v$;
--   4. if the values on $G$ are independent across source nodes, so are the values $w_{e'}=w_e$ on $G_i$.
--
--   The proof of Theorem 4 relies on this when it runs "the algorithm given by Theorem 3 on $G_i$".
--
--   Differences from the source:
--   - encoding: a DAG $G=(V,E)$ with start $s$, target $t$ and parallel edges → `Graph` extends the published multigraph `Network` (an edge type with `tail`, `head`); `Acyclic` means no nonempty closed walk; a path is an edge list chained by `IsPathFrom`; reason: same instances: a finite graph has no closed walk exactly when it is a DAG, and in a DAG every walk is a path
--   - encoding: a finite graph and a finite label set $L$ → `[Fintype V] [Fintype E] [Fintype L]`, with `V E L : Type`; reason: finite data; every finite type is equivalent to one in `Type`
--   - encoding: edges that start in different nodes are independent; edges that start in the same node can be arbitrarily correlated → `IndepAcrossNodes`: the vectors $(W_e)_{\mathrm{tail}(e)=u}$, $u\in V$, are mutually independent; nothing is assumed within a node; reason: the paper's assumption, stated for the out-edge vectors
--   - reading: $L_e \subset L$ → `labels e : Finset L`, i.e. $L_e\subseteq L$; reason: with one label the labelled edges of the $m$-choice example (p.5) have $L_e=L$; the strict reading would exclude it
--   - encoding: $G_i$: nodes $V(P_i)$, the edges between them, and an artificial edge $e'=(u,v')$ with $w_{e'}=w_e$ for each edge $e=(u,v)$ with $u\in V(P_i)$, $v\notin V(P_i)$ → `focal G (P i)`: nodes $\{t\}\cup V(P_i)$; edges the edges $e$ of $G$ with $\mathrm{tail}(e)\in V(P_i)$, the artificial $e'$ being $e$ itself with head $v'$ (head $t$ if no node of $V(P_i)$ is reachable); values $w\circ$`Subtype.val`; labels copied; reason: the same graph whenever $P_i$ is an $s,t$-path and every node reaches $t$, which the hypotheses guarantee
--   - reading: "it runs the algorithm given by Theorem 3 on $G_i$" (implicit: $G_i$ satisfies the hypotheses of Theorem 3) → explicit conjuncts: acyclic, covered by one $s,t$-path, $|L_e|\le d$, $c_\ell\ge1$, parallel unlabelled edges, independence across source nodes, and the existence and reachability of $v'$; reason: these are exactly the hypotheses Theorem 3 needs on $G_i$, together with the paper's sentence on $v'$
--   - encoding: a capacity $c_\ell\ge1$ for each label, with $|P\cap E(\ell)|\le c_\ell$ → `cap : L → ℕ` (natural-number capacities); reason: an edge count is an integer, so $|P\cap E(\ell)|\le c_\ell$ exactly when $|P\cap E(\ell)|\le\lfloor c_\ell\rfloor$, and $\lfloor c_\ell\rfloor\ge1$; same instances
-- source:
--   Cristi, Oren, Planning Against a Prophet: A Graph-Theoretic Framework for Making Sequential Decisions, arXiv:2406.13911v1, §4.1 Proof of Theorem 4, p.12, "Note that there is always a path from v to t … every edge that starts in a node in V(Pi) is represented"

import Mathlib
import Definitions.Def_PlanningProphet_FocalGraph

open scoped NNReal ENNReal
open MeasureTheory

universe u

namespace PlanningProphet

/-- **`Gᵢ` is a width-1 instance** (Cristi–Oren, arXiv:2406.13911v1, §4.1, p.12).
"Note that there is always a path from `v` to `t`, and `t ∈ V(Pᵢ)`, so there is always a node
`v′`. We add an edge `e′ = (u, v′)` with value `w_{e′} := w_e`. We call these edges artificial.
Note that with this construction, every edge that starts in a node in `V(Pᵢ)` is represented."

Let `G` be a DAG covered by the `s,t`-paths `P₁, …, P_k`, with at most `d` labels per edge,
`c_ℓ ≥ 1` and parallel unlabelled edges. Then for each `i`:
1. `Gᵢ` is acyclic and is covered by a single `s,t`-path (width 1);
2. `Gᵢ` has at most `d` labels per edge, `c_ℓ ≥ 1` and parallel unlabelled edges;
3. for an edge `e = (u, v)` with `u ∈ V(Pᵢ)` and `v ∉ V(Pᵢ)`, some node of `V(Pᵢ)` is reachable
   from `v` ("there is always a node `v′`"), and the head of `e` in `Gᵢ` is a node of `V(Pᵢ)`
   reachable from `v`;
4. if the values on `G` are independent across source nodes, so are the values `w ∘ Subtype.val`
   on `Gᵢ`.

This is what lets the proof run "the algorithm given by Theorem 3 on `Gᵢ`" (p.12). Every edge
of `G` starting in `V(Pᵢ)` is an edge of `Gᵢ` by construction (`Graph.focal`). -/
theorem focal_width_one {V E L : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype L] [DecidableEq L] (G : Graph V E L) (hG : G.Acyclic) {k : ℕ}
    (P : Fin k → List E) (hP : G.CoveredBy P)
    (d : ℕ) (hd : G.LabelsAtMost d) (hcap : G.CapPos) (hpar : G.ParallelUnlabeled) (i : Fin k) :
    (G.focal (P i)).Acyclic ∧
    (∃ Q, (G.focal (P i)).IsSTPath Q ∧ ∀ v, v ∈ (G.focal (P i)).vertices Q) ∧
    (G.focal (P i)).LabelsAtMost d ∧ (G.focal (P i)).CapPos ∧
    (G.focal (P i)).ParallelUnlabeled ∧
    (∀ e : {e : E // G.tail e ∈ G.vertices (P i)}, G.head e.1 ∉ G.vertices (P i) →
      (∃ v ∈ G.vertices (P i), G.Reach (G.head e.1) v) ∧
      ((G.focal (P i)).head e).1 ∈ G.vertices (P i) ∧
      G.Reach (G.head e.1) ((G.focal (P i)).head e).1) ∧
    (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (W : Ω → E → ℝ≥0),
      G.IndepAcrossNodes W μ → (G.focal (P i)).IndepAcrossNodes (fun ω e => W ω e.1) μ) := by sorry

end PlanningProphet
