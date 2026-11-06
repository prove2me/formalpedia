-- Prove2me | Theorems.Thm_PlanningProphet_theorem_3
-- name    : PlanningProphet.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:12:45.57065+00:00
-- url     : https://prove2.me/theorems/37dc5735-747a-4088-bacd-a92816d3faa2
-- title:
--   Theorem 3 — width 1 with at most $d$ labels per edge: an online policy earns $\frac1{d+2}\mathbb E(OPT)$
-- statement:
--   Let $G$ be a DAG with start $s$ and target $t$ that is covered by a single $s,t$-path $P$ ($V(P)=V$, the width-1 setting of §3). Suppose every edge has at most $d$ labels, every capacity satisfies $c_\ell\ge 1$, and every labelled edge has a parallel unlabelled edge. Let the values $W$ be non-negative random variables, independent across source nodes and arbitrarily correlated within a node. Then there is an online policy $ALG$, randomized with a seed independent of the values, that always selects a feasible $s,t$-path and satisfies
--   $$\mathbb E(ALG)\ \ge\ \frac{1}{d+2}\,\mathbb E(OPT).$$
--
--   For $d=0$ (no labels) this is the $1/2$ of Theorem 2, which contains the classic single-item prophet inequality (Figure 1). Theorem 4 applies it to each graph $G_i$.
--
--   Differences from the source:
--   - encoding: a DAG $G=(V,E)$ with start $s$, target $t$ and parallel edges → `Graph` extends the published multigraph `Network` (an edge type with `tail`, `head`); `Acyclic` means no nonempty closed walk; a path is an edge list chained by `IsPathFrom`; reason: same instances: a finite graph has no closed walk exactly when it is a DAG, and in a DAG every walk is a path
--   - encoding: a finite graph and a finite label set $L$ → `[Fintype V] [Fintype E] [Fintype L]`, with `V E L : Type`; reason: finite data; every finite type is equivalent to one in `Type`
--   - encoding: non-negative random values $w_e$ and expectations $\mathbb E(\cdot)$ → a measurable `W : Ω → E → ℝ≥0` on a probability space $(\Omega,\mu)$; expectations are lower Lebesgue integrals in `ℝ≥0∞`; reason: for non-negative values the lower integral is the expectation, finite or infinite; no integrability hypothesis is needed
--   - encoding: edges that start in different nodes are independent; edges that start in the same node can be arbitrarily correlated → `IndepAcrossNodes`: the vectors $(W_e)_{\mathrm{tail}(e)=u}$, $u\in V$, are mutually independent; nothing is assumed within a node; reason: the paper's assumption, stated for the out-edge vectors
--   - reading: $L_e \subset L$ → `labels e : Finset L`, i.e. $L_e\subseteq L$; reason: with one label the labelled edges of the $m$-choice example (p.5) have $L_e=L$; the strict reading would exclude it
--   - encoding: $OPT=\max_{P\in\mathcal P}\sum_{e\in P}w_e$ over feasible $s,t$-paths → `opt`: the supremum in `ℝ≥0∞` over label-feasible $s,t$-paths; reason: the set is finite and, under the hypotheses, nonempty, so the supremum is the maximum
--   - reading: an algorithm or policy $ALG$ that determines at each node which edge to follow next, given the observed realizations so far, where $w_e$ is observed when the tail of $e$ is reached → an `OnlinePolicy` with a seed space $\Xi$ and seed law $\nu$: the decision reads $w$ only on edges leaving visited nodes; the seed is independent of the values (expectation under $\nu\otimes\mu$); the run is a label-feasible $s,t$-path for every seed and value vector; the run is cut off after $|V|$ steps; reason: the model of p.6; the algorithms of pp.8–12 are randomized, their coins drawn independently of everything else; an $s,t$-path of a DAG has fewer than $|V|$ edges
--   - reading: $\mathbb E(ALG)$, an expectation → an extra conjunct: the selected path is a random variable (`RunMeasurable`: each event $\{ALG\text{ selects }p\}$ is measurable); reason: an expectation presupposes a random variable; the conjunct only strengthens the conclusion
--   - encoding: a width-1 graph (§3) → one $s,t$-path $P$ with every node in $V(P)$; reason: Theorem 2's own gloss of width 1: "there is an $s,t$-path such that $V(P)=V$"
--   - encoding: a capacity $c_\ell\ge1$ for each label, with $|P\cap E(\ell)|\le c_\ell$ → `cap : L → ℕ` (natural-number capacities); reason: an edge count is an integer, so $|P\cap E(\ell)|\le c_\ell$ exactly when $|P\cap E(\ell)|\le\lfloor c_\ell\rfloor$, and $\lfloor c_\ell\rfloor\ge1$; same instances
-- source:
--   Cristi, Oren, Planning Against a Prophet: A Graph-Theoretic Framework for Making Sequential Decisions, arXiv:2406.13911v1, Theorem 3, p.9 (§3 Width 1 Graphs, §3.2 Width 1 Graphs with Edge Labels)

import Mathlib
import Definitions.Def_PlanningProphet_OnlinePolicy

open scoped NNReal ENNReal
open MeasureTheory

universe u

namespace PlanningProphet

/-- **Theorem 3** (Cristi–Oren, *Planning Against a Prophet*, arXiv:2406.13911v1, p.9).
"If each edge has at most `d` labels, then there is an algorithm ALG such that
`E(ALG) ≥ 1/(d+2) E(OPT)`."

The theorem is stated in §3, "Width 1 Graphs: Single Focal Path with Bypasses", §3.2 "Width 1
Graphs with Edge Labels": the graph is covered by one `s,t`-path `P` (`V(P) = V`), with the
standing assumptions of §2 (a DAG, `c_ℓ ≥ 1`, parallel unlabelled edges, nonnegative values
independent across source nodes, arbitrarily correlated within a node).

**Formalization Note.** "An algorithm" is a randomized online policy (`OnlinePolicy`: it reads the
value of an edge only once the edge's tail has been reached) with a seed space `Ξ` and a seed law
`ν` independent of the values, whose run is a label-feasible `s,t`-path for every seed and every
value vector, and whose selected path is a random variable (`RunMeasurable`). `E(ALG)` and
`E(OPT)` are lower Lebesgue integrals in `ℝ≥0∞`. -/
theorem theorem_3 {V E L : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype L] [DecidableEq L] (G : Graph V E L) (hG : G.Acyclic) (P : List E)
    (hP : G.IsSTPath P) (hPcov : ∀ v, v ∈ G.vertices P)
    (d : ℕ) (hd : G.LabelsAtMost d) (hcap : G.CapPos) (hpar : G.ParallelUnlabeled)
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → E → ℝ≥0) (hW : Measurable W) (hind : G.IndepAcrossNodes W μ) :
    ∃ (Ξ : Type u) (_ : MeasurableSpace Ξ) (ν : Measure Ξ) (π : OnlinePolicy G Ξ),
      IsProbabilityMeasure ν ∧ π.IsFeasibleRun ∧ π.RunMeasurable W ∧
      1 / ((d : ℝ≥0∞) + 2) * G.expectedOpt μ W ≤ π.expectedAlg ν μ W := by sorry

end PlanningProphet
