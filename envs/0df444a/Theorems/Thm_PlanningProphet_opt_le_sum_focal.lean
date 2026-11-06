-- Prove2me | Theorems.Thm_PlanningProphet_opt_le_sum_focal
-- name    : PlanningProphet.opt_le_sum_focal
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:12:47.517228+00:00
-- url     : https://prove2.me/theorems/8acefb16-0bb0-4388-9462-ab0de746677f
-- title:
--   §4.1, p.12 — $\mathbb E(OPT)\le\sum_{i=1}^k\mathbb E(OPT(G_i))$
-- statement:
--   Let $G$ be a DAG covered by the $s,t$-paths $P_1,\dots,P_k$, in which every labelled edge has a parallel unlabelled edge. Let $W$ be a non-negative random value vector on a probability space. Then
--   $$\mathbb E(OPT)\ \le\ \sum_{i=1}^k \mathbb E\big(OPT(G_i)\big),$$
--   where $OPT(G_i)$ is computed with the values $w_{e'}=w_e$ on the graph $G_i$ of §4.1.
--
--   This is the upper bound on the prophet that the proof of Theorem 4 combines with Theorem 3.
--
--   Differences from the source:
--   - encoding: a DAG $G=(V,E)$ with start $s$, target $t$ and parallel edges → `Graph` extends the published multigraph `Network` (an edge type with `tail`, `head`); `Acyclic` means no nonempty closed walk; a path is an edge list chained by `IsPathFrom`; reason: same instances: a finite graph has no closed walk exactly when it is a DAG, and in a DAG every walk is a path
--   - encoding: a finite graph and a finite label set $L$ → `[Fintype V] [Fintype E] [Fintype L]`, with `V E L : Type`; reason: finite data; every finite type is equivalent to one in `Type`
--   - encoding: non-negative random values $w_e$ and expectations $\mathbb E(\cdot)$ → a measurable `W : Ω → E → ℝ≥0` on a probability space $(\Omega,\mu)$; expectations are lower Lebesgue integrals in `ℝ≥0∞`; reason: for non-negative values the lower integral is the expectation, finite or infinite; no integrability hypothesis is needed
--   - reading: $L_e \subset L$ → `labels e : Finset L`, i.e. $L_e\subseteq L$; reason: with one label the labelled edges of the $m$-choice example (p.5) have $L_e=L$; the strict reading would exclude it
--   - encoding: $OPT=\max_{P\in\mathcal P}\sum_{e\in P}w_e$ over feasible $s,t$-paths → `opt`: the supremum in `ℝ≥0∞` over label-feasible $s,t$-paths; reason: the set is finite and, under the hypotheses, nonempty, so the supremum is the maximum
--   - encoding: $G_i$: nodes $V(P_i)$, the edges between them, and an artificial edge $e'=(u,v')$ with $w_{e'}=w_e$ for each edge $e=(u,v)$ with $u\in V(P_i)$, $v\notin V(P_i)$ → `focal G (P i)`: nodes $\{t\}\cup V(P_i)$; edges the edges $e$ of $G$ with $\mathrm{tail}(e)\in V(P_i)$, the artificial $e'$ being $e$ itself with head $v'$ (head $t$ if no node of $V(P_i)$ is reachable); values $w\circ$`Subtype.val`; labels copied; reason: the same graph whenever $P_i$ is an $s,t$-path and every node reaches $t$, which the hypotheses guarantee
--   - generalization: the hypotheses of Theorem 4 (at most $d$ labels per edge, $c_\ell\ge1$, independence across source nodes) → none of these three is assumed; reason: the inequality holds realization by realization and uses only the cover and the parallel unlabelled edges; the paper's case is included
--   - encoding: a capacity $c_\ell\ge1$ for each label, with $|P\cap E(\ell)|\le c_\ell$ → `cap : L → ℕ` (natural-number capacities); reason: an edge count is an integer, so $|P\cap E(\ell)|\le c_\ell$ exactly when $|P\cap E(\ell)|\le\lfloor c_\ell\rfloor$, and $\lfloor c_\ell\rfloor\ge1$; same instances
-- source:
--   Cristi, Oren, Planning Against a Prophet: A Graph-Theoretic Framework for Making Sequential Decisions, arXiv:2406.13911v1, §4.1 Proof of Theorem 4, p.12, display E(OPT) ≤ Σ_{i=1}^k E(OPT(G_i))

import Mathlib
import Definitions.Def_PlanningProphet_FocalGraph
import Definitions.Def_PlanningProphet_OnlinePolicy

open scoped NNReal ENNReal
open MeasureTheory

universe u

namespace PlanningProphet

/-- **`E(OPT) ≤ Σᵢ E(OPT(Gᵢ))`** (Cristi–Oren, arXiv:2406.13911v1, §4.1, p.12, display).
"Let `OPT(Gᵢ)` denote the optimal path in the graph `Gᵢ`. Since all edges in the original graph
are represented by some edge in one of the new graphs, we have that
`E(OPT) ≤ Σ_{i=1}^k E(OPT(Gᵢ))`."

`G` is a DAG covered by the `s,t`-paths `P₁, …, P_k`, with parallel unlabelled edges; the values
`W` are a random vector under a probability measure `μ`, and the values on `Gᵢ` are
`W ∘ Subtype.val`. -/
theorem opt_le_sum_focal {V E L : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype L] [DecidableEq L] (G : Graph V E L) (hG : G.Acyclic) {k : ℕ}
    (P : Fin k → List E) (hP : G.CoveredBy P) (hpar : G.ParallelUnlabeled)
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → E → ℝ≥0) (hW : Measurable W) :
    G.expectedOpt μ W ≤ ∑ i, (G.focal (P i)).expectedOpt μ (fun ω e => W ω e.1) := by sorry

end PlanningProphet
