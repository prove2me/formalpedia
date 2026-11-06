-- Prove2me | Theorems.Thm_PlanningProphet_focal_dominates
-- name    : PlanningProphet.focal_dominates
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:13:01.906738+00:00
-- url     : https://prove2.me/theorems/7affc9ee-2a38-4a3a-af84-00ffda5030d0
-- title:
--   §4.1, p.12 — a path of $G_i$ is worth at least $OPT\cap E^+(P_i)$
-- statement:
--   Let $G$ be a DAG covered by the $s,t$-paths $P_1,\dots,P_k$, in which every labelled edge has a parallel unlabelled edge. Let $E^+(P_i)$ be the set of edges that start at a node of $V(P_i)$. Then for every $i$, every value vector $w\ge0$, and every feasible $s,t$-path $p$ of $G$,
--   $$\sum_{e\in p\,\cap\,E^+(P_i)} w_e\ \le\ OPT_{G_i}(w),$$
--   where $OPT_{G_i}$ is the best feasible $s,t$-path of $G_i$ under the values $w_{e'}=w_e$.
--
--   Taking $p$ to be $OPT$'s path gives the paper's sentence. Summing over $i$ yields $\mathbb E(OPT)\le\sum_i\mathbb E(OPT(G_i))$.
--
--   Differences from the source:
--   - encoding: a DAG $G=(V,E)$ with start $s$, target $t$ and parallel edges → `Graph` extends the published multigraph `Network` (an edge type with `tail`, `head`); `Acyclic` means no nonempty closed walk; a path is an edge list chained by `IsPathFrom`; reason: same instances: a finite graph has no closed walk exactly when it is a DAG, and in a DAG every walk is a path
--   - encoding: a finite graph and a finite label set $L$ → `[Fintype V] [Fintype E] [Fintype L]`, with `V E L : Type`; reason: finite data; every finite type is equivalent to one in `Type`
--   - reading: $L_e \subset L$ → `labels e : Finset L`, i.e. $L_e\subseteq L$; reason: with one label the labelled edges of the $m$-choice example (p.5) have $L_e=L$; the strict reading would exclude it
--   - encoding: $OPT=\max_{P\in\mathcal P}\sum_{e\in P}w_e$ over feasible $s,t$-paths → `opt`: the supremum in `ℝ≥0∞` over label-feasible $s,t$-paths; reason: the set is finite and, under the hypotheses, nonempty, so the supremum is the maximum
--   - encoding: $G_i$: nodes $V(P_i)$, the edges between them, and an artificial edge $e'=(u,v')$ with $w_{e'}=w_e$ for each edge $e=(u,v)$ with $u\in V(P_i)$, $v\notin V(P_i)$ → `focal G (P i)`: nodes $\{t\}\cup V(P_i)$; edges the edges $e$ of $G$ with $\mathrm{tail}(e)\in V(P_i)$, the artificial $e'$ being $e$ itself with head $v'$ (head $t$ if no node of $V(P_i)$ is reachable); values $w\circ$`Subtype.val`; labels copied; reason: the same graph whenever $P_i$ is an $s,t$-path and every node reaches $t$, which the hypotheses guarantee
--   - generalization: the edges of $OPT$'s path → every feasible $s,t$-path $p$ of $G$; reason: $OPT$'s path is a feasible $s,t$-path, so the paper's case is included
--   - reading: "there is always a path in $G_i$" with at least that value → the value is at most $OPT_{G_i}$, the maximum over feasible $s,t$-paths of $G_i$; reason: the next sentence uses it as a bound on $OPT(G_i)$, which satisfies the same label constraint
--   - generalization: the standing assumptions at most $d$ labels per edge (Theorem 4) and $c_\ell\ge1$ (p.7) → not assumed; reason: the inequality holds value vector by value vector and uses only acyclicity, the cover and the parallel unlabelled edges; the paper's case is included
--   - encoding: a capacity $c_\ell\ge1$ for each label, with $|P\cap E(\ell)|\le c_\ell$ → `cap : L → ℕ` (natural-number capacities); reason: an edge count is an integer, so $|P\cap E(\ell)|\le c_\ell$ exactly when $|P\cap E(\ell)|\le\lfloor c_\ell\rfloor$, and $\lfloor c_\ell\rfloor\ge1$; same instances
-- source:
--   Cristi, Oren, Planning Against a Prophet: A Graph-Theoretic Framework for Making Sequential Decisions, arXiv:2406.13911v1, §4.1 Proof of Theorem 4, p.12, "There is always a path in Gi with a value at least as large as the value of the edges in OPT ∩ E+(Pi)"

import Mathlib
import Definitions.Def_PlanningProphet_FocalGraph

open scoped NNReal ENNReal
open MeasureTheory

universe u

namespace PlanningProphet

/-- **A path of `Gᵢ` dominates `OPT ∩ E⁺(Pᵢ)`** (Cristi–Oren, arXiv:2406.13911v1, §4.1, p.12).
"Let `E⁺(Pᵢ)` be the set of edges that start in a node in `V(Pᵢ)`. There is always a path in `Gᵢ`
with a value at least as large as the value of the edges in `OPT ∩ E⁺(Pᵢ)`."

Stated for every label-feasible `s,t`-path `p` of `G` (`OPT`'s path is one): the total value of
the edges of `p` that start in `V(Pᵢ)` is at most `OPT(Gᵢ)`, the best label-feasible
`s,t`-path of `Gᵢ` under the values `w ∘ Subtype.val`. `G` is a DAG covered by `P₁, …, P_k`, with
parallel unlabelled edges. -/
theorem focal_dominates {V E L : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype L] [DecidableEq L] (G : Graph V E L) (hG : G.Acyclic) {k : ℕ}
    (P : Fin k → List E) (hP : G.CoveredBy P) (hpar : G.ParallelUnlabeled) (i : Fin k)
    (w : E → ℝ≥0) (p : List E) (hp : G.IsSTPath p) (hpl : G.LabelFeasible p) :
    pathValue w (p.filter fun e => decide (G.tail e ∈ G.vertices (P i))) ≤
      (G.focal (P i)).opt (fun e => w e.1) := by sorry

end PlanningProphet
