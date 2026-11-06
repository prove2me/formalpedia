-- Prove2me | Theorems.Thm_PlanningProphet_theorem_4
-- name    : PlanningProphet.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:12:48.248195+00:00
-- url     : https://prove2.me/theorems/7edf90e0-909e-4d3d-9e3d-294af102dd0f
-- title:
--   Theorem 4 — a DAG covered by $k$ paths, at most $d$ labels per edge: an online policy earns $\frac{1}{k(d+2)}\mathbb E(OPT)$
-- statement:
--   Let $G$ be a DAG with start $s$ and target $t$ that is covered by $k$ $s,t$-paths $P_1,\dots,P_k$, i.e. $V=\bigcup_i V(P_i)$. Suppose every edge has at most $d$ labels, every capacity satisfies $c_\ell\ge1$, and every labelled edge has a parallel unlabelled edge. Let the values $W$ be non-negative random variables, independent across source nodes and arbitrarily correlated within a node. Let $OPT$ be the value of the best feasible $s,t$-path. Then there is an online policy $ALG$ with the following properties. It is randomized with a seed independent of the values. It observes $w_e$ only once the tail of $e$ has been reached. For every seed and every realization it selects a feasible $s,t$-path. Finally,
--   $$\mathbb E(ALG)\ \ge\ \frac{1}{k\,(d+2)}\,\mathbb E(OPT).$$
--
--   This is the main result of the paper. For $d=0$ (no labels) the constant is $\frac1{2k}$. For $k=1$ it is Theorem 3.
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
--   - generalization: the graph has width $k$ (the least number of covering $s,t$-paths is $k$) → the graph is covered by some $k$ $s,t$-paths; reason: a graph of width $k$ is covered by $k$ paths; a graph covered by $k$ paths has width $k'\le k$, and the bound $\frac1{k'(d+2)}$ is at least $\frac1{k(d+2)}$
--   - encoding: a capacity $c_\ell\ge1$ for each label, with $|P\cap E(\ell)|\le c_\ell$ → `cap : L → ℕ` (natural-number capacities); reason: an edge count is an integer, so $|P\cap E(\ell)|\le c_\ell$ exactly when $|P\cap E(\ell)|\le\lfloor c_\ell\rfloor$, and $\lfloor c_\ell\rfloor\ge1$; same instances
-- source:
--   Cristi, Oren, Planning Against a Prophet: A Graph-Theoretic Framework for Making Sequential Decisions, arXiv:2406.13911v1, Theorem 4, p.12 (model §2 pp.6–7; proof §4.1 pp.12–13)

import Mathlib
import Definitions.Def_PlanningProphet_OnlinePolicy

open scoped NNReal ENNReal
open MeasureTheory

universe u

namespace PlanningProphet

/-- **Theorem 4** (Cristi–Oren, *Planning Against a Prophet*, arXiv:2406.13911v1, p.12).
"If the graph has width `k` and each edge has at most `d` labels, then there is an algorithm ALG
that satisfies `E(ALG) ≥ 1/(k·(d+2)) E(OPT)`."

`G` is a DAG with start `s` and target `t` (§2), covered by `k` `s,t`-paths `P₁, …, P_k`
(`V = ⋃ᵢ V(Pᵢ)`), every edge carrying at most `d` labels, every capacity `c_ℓ ≥ 1`, every labelled
edge having a parallel unlabelled edge (p.7). The values `W` are nonnegative, random under a
probability measure `μ`, independent across source nodes and arbitrarily correlated within a
node (p.7). `OPT` is the best label-feasible `s,t`-path (p.7).

**Formalization Note.** "Width `k`" (the least number of covering `s,t`-paths is `k`) is
replaced by "covered by `k` `s,t`-paths": a graph of width `k` is covered by `k` paths, and a
graph covered by `k` paths has width `k′ ≤ k`, for which the bound `1/(k′(d+2))` is larger.
"An algorithm" is a randomized online policy (`OnlinePolicy`: the decision reads the value of an
edge only once its tail is reached) with a seed space `Ξ` and seed law `ν` independent of the
values, whose run is a label-feasible `s,t`-path for every seed and value vector and is a random
variable. `E(ALG)` and `E(OPT)` are lower Lebesgue integrals in `ℝ≥0∞`. A cover forces `k ≥ 1`
(the node `s` lies on some `Pᵢ`), so the constant `1/(k(d+2))` is never `1/0`. -/
theorem theorem_4 {V E L : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype L] [DecidableEq L] (G : Graph V E L) (hG : G.Acyclic) {k : ℕ}
    (P : Fin k → List E) (hP : G.CoveredBy P)
    (d : ℕ) (hd : G.LabelsAtMost d) (hcap : G.CapPos) (hpar : G.ParallelUnlabeled)
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → E → ℝ≥0) (hW : Measurable W) (hind : G.IndepAcrossNodes W μ) :
    ∃ (Ξ : Type u) (_ : MeasurableSpace Ξ) (ν : Measure Ξ) (π : OnlinePolicy G Ξ),
      IsProbabilityMeasure ν ∧ π.IsFeasibleRun ∧ π.RunMeasurable W ∧
      1 / ((k : ℝ≥0∞) * ((d : ℝ≥0∞) + 2)) * G.expectedOpt μ W ≤ π.expectedAlg ν μ W := by sorry

end PlanningProphet
