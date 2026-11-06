-- Prove2me | Theorems.Thm_PlanningProphet_lemma_2
-- name    : PlanningProphet.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:13:46.489976+00:00
-- url     : https://prove2.me/theorems/503a3f18-1607-443f-b0d4-28ac0b2ac474
-- title:
--   Lemma 2 — the focal-path algorithm is well defined and selects each edge with probability $x_e/(d+2)$
-- statement:
--   Let $G$ be a DAG whose edges carry at most $d$ labels each, with capacities $c_\ell\ge1$ and a parallel unlabelled edge for every labelled edge. Let $P$ be an unlabelled $s,t$-path visiting every node (the width-1 setting of §3). Let the values $W$ be non-negative and independent across source nodes, and let $x_e$ be the probability that $OPT$ takes $e$, for any measurable choice of $OPT$'s path. Let $ALG$ be the algorithm of §3.2, run on $P$. Then:
--
--   1. **$ALG$ is well defined.** An acceptance rule $q(e)=\min\{1,1/((d+2)p_q(e))\}$ exists. For every such rule,
--   $$p(e)\ \ge\ \frac1{d+2}\qquad\text{for every edge } e,$$
--   so $\frac1{d+2}\cdot\frac1{p(e)}\in[0,1]$.
--   2. **Off the path.** For every $e\notin P$,
--   $$\Pr[e \text{ is marked as tentative and selected by } ALG]=\frac{x_e}{d+2}.$$
--   3. **On the path.** For every $e\in P$,
--   $$\Pr[e \text{ is marked as tentative and selected by } ALG]\ \ge\ \frac{x_e}{d+2}.$$
--
--   Summed against $\mathbb E(w_e\mid OPT\text{ takes }e)$, these probabilities give Theorem 3.
--
--   Differences from the source:
--   - encoding: a DAG $G=(V,E)$ with start $s$, target $t$ and parallel edges → `Graph` extends the published multigraph `Network` (an edge type with `tail`, `head`); `Acyclic` means no nonempty closed walk; a path is an edge list chained by `IsPathFrom`; reason: same instances: a finite graph has no closed walk exactly when it is a DAG, and in a DAG every walk is a path
--   - encoding: a finite graph and a finite label set $L$ → `[Fintype V] [Fintype E] [Fintype L]`, with `V E L : Type`; reason: finite data; every finite type is equivalent to one in `Type`
--   - encoding: non-negative random values $w_e$ and expectations $\mathbb E(\cdot)$ → a measurable `W : Ω → E → ℝ≥0` on a probability space $(\Omega,\mu)$; expectations are lower Lebesgue integrals in `ℝ≥0∞`; reason: for non-negative values the lower integral is the expectation, finite or infinite; no integrability hypothesis is needed
--   - encoding: edges that start in different nodes are independent; edges that start in the same node can be arbitrarily correlated → `IndepAcrossNodes`: the vectors $(W_e)_{\mathrm{tail}(e)=u}$, $u\in V$, are mutually independent; nothing is assumed within a node; reason: the paper's assumption, stated for the out-edge vectors
--   - reading: $L_e \subset L$ → `labels e : Finset L`, i.e. $L_e\subseteq L$; reason: with one label the labelled edges of the $m$-choice example (p.5) have $L_e=L$; the strict reading would exclude it
--   - reading: "ALG is well-defined" → an acceptance rule solving $q(e)=\min\{1,1/((d+2)p_q(e))\}$ exists, and every solution has $1/(d+2)\le p_q(e)$ for every edge; reason: the proof's first sentence: "We need to show that $\frac1{d+2}\cdot\frac1{p(e)}\in[0,1]$"; $p$ is defined recursively along $P$, so the solution is unique
--   - reading: $x_e$, the probability that $OPT$ takes $e$, with no tie-breaking rule → for every measurable selector `sel` of a feasible $s,t$-path of value $OPT$, $x_e=\mu\{e\in\mathrm{sel}(W)\}$, the same `sel` giving $OPT(i)$; reason: the paper fixes no tie-breaking; every measurable choice is covered
--   - reading: "it samples $OPT$ conditional on the given values of the edges that leave $i$" → `sel` applied to the vector equal to the true values on the edges leaving $i$ and to an independent copy $W(\omega'_i)$ elsewhere; reason: by independence across source nodes this vector has the conditional law, and it is independent of everything else
--   - encoding: "$ALG$ takes $e$ with probability $\frac1{d+2}\cdot\frac1{p(e)}$, independently of everything else" → an independent uniform coin $c_i\in[0,1]$ per node; $e$ is taken when $c_i<q(e)$; reason: $\Pr[c_i<q]=q$ for $q\in[0,1]$
--   - reading: "Otherwise, $ALG$ takes the next edge in $P$" → `pathEdge P i`, the edge of $P$ leaving $i$; reason: with parallel edges, the next edge of $P$ is $P$'s own edge out of $i$
--   - reading: "$e$ is marked as tentative and is selected by $ALG$" → when the run is at $\mathrm{tail}(e)$, the tentative edge is $e$ and the run's next edge is $e$; reason: the event used in the proofs of Lemma 2 and Theorem 3; for $e\in P$ the fallback edge is $e$ itself
--   - encoding: a capacity $c_\ell\ge1$ for each label, with $|P\cap E(\ell)|\le c_\ell$ → `cap : L → ℕ` (natural-number capacities); reason: an edge count is an integer, so $|P\cap E(\ell)|\le c_\ell$ exactly when $|P\cap E(\ell)|\le\lfloor c_\ell\rfloor$, and $\lfloor c_\ell\rfloor\ge1$; same instances
-- source:
--   Cristi, Oren, Planning Against a Prophet: A Graph-Theoretic Framework for Making Sequential Decisions, arXiv:2406.13911v1, Lemma 2, p.10 (algorithm pp.9–10)

import Mathlib
import Definitions.Def_PlanningProphet_FocalAlgorithm

open scoped NNReal ENNReal
open MeasureTheory

universe u

namespace PlanningProphet

/-- **Lemma 2** (Cristi–Oren, *Planning Against a Prophet*, arXiv:2406.13911v1, p.10).
"ALG is well-defined and for every `e ∈ E∖P`, the probability that `e` is marked as tentative and
is selected by ALG is exactly `x_e/(d + 2)`. For every `e ∈ P` this probability is at least
`x_e/(d + 2)`."

`ALG` is the algorithm of §3.2 (pp.9–10), `Graph.focalPath`, run on a graph of width 1 (§3: an
unlabelled `s,t`-path `P` visits all nodes, p.9) whose edges carry at most `d` labels, with the
standing assumptions of §2 (a DAG, `c_ℓ ≥ 1`, parallel unlabelled edges, nonnegative values
independent across source nodes). "Well-defined" is the existence of the recursively defined
acceptance rule together with `1/(d+2) ≤ p(e)` for every edge, so that `1/(d+2) · 1/p(e) ∈ [0,1]`
(the first sentence of the proof).

**Formalization Note.** The acceptance rule `q` is any solution of
`q e = min 1 (1/((d+2) p_q(e)))` (`IsFocalRule`); the first conjunct says one exists, and the
others hold for every solution (there is exactly one, by recursion along `P`). Probabilities are
under `seedMeasure μ ⊗ μ`: one copy of the sample and one uniform coin per node, independent of
the values. `OPT`'s path is chosen by an arbitrary measurable maximizer `sel` (the paper fixes no
tie-breaking), used both for `x_e = optProb` and for the samples `OPT(i)`. -/
theorem lemma_2 {V E L : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype L] [DecidableEq L] (G : Graph V E L) (hG : G.Acyclic) (P : List E)
    (hP : G.IsSTPath P) (hPcov : ∀ v, v ∈ G.vertices P) (hPunl : ∀ e ∈ P, G.labels e = ∅)
    (d : ℕ) (hd : G.LabelsAtMost d) (hcap : G.CapPos) (hpar : G.ParallelUnlabeled)
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → E → ℝ≥0) (hW : Measurable W) (hind : G.IndepAcrossNodes W μ)
    (sel : (E → ℝ≥0) → List E) (hsel : G.IsOptSelector sel) :
    (∃ q : E → ℝ≥0∞, G.IsFocalRule sel P W μ d q) ∧
    ∀ q : E → ℝ≥0∞, G.IsFocalRule sel P W μ d q →
      (∀ e, 1 / ((d : ℝ≥0∞) + 2) ≤ G.feasProb sel P W μ q e) ∧
      (∀ e, e ∉ P → G.selProb sel P W μ q e = Graph.optProb μ W sel e / ((d : ℝ≥0∞) + 2)) ∧
      (∀ e ∈ P, Graph.optProb μ W sel e / ((d : ℝ≥0∞) + 2) ≤ G.selProb sel P W μ q e) := by sorry

end PlanningProphet
