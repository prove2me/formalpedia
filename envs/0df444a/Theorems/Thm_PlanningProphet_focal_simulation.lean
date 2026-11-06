-- Prove2me | Theorems.Thm_PlanningProphet_focal_simulation
-- name    : PlanningProphet.focal_simulation
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:13:00.645332+00:00
-- url     : https://prove2.me/theorems/0dc6a26e-2270-40b1-85b1-4a020f195536
-- title:
--   §4.1, p.12 — a policy on $G_i$ runs in $G$ with at least its value
-- statement:
--   Let $G$ be a DAG covered by the $s,t$-paths $P_1,\dots,P_k$, in which every labelled edge has a parallel unlabelled edge. Fix $i$ and an online policy $\pi$ on $G_i$ with seed space $\Xi$. Suppose $\pi$ always selects a feasible $s,t$-path of $G_i$, and its selected path is a random variable for the values $w_{e'}=w_e$. Then there is an online policy $\pi'$ on $G$ with the same seed space such that
--
--   1. $\pi'$ always selects a feasible $s,t$-path of $G$, and its selected path is a random variable;
--   2. for every seed $\xi$ and every value vector $w$,
--   $$ALG_{\pi'}(\xi,w)\ \ge\ ALG_{\pi}(\xi,\,w|_{G_i}).$$
--
--   The policy $\pi'$ takes an edge of $G_i$ that starts and ends in $V(P_i)$ as the same edge of $G$, and an artificial edge as the corresponding path of $G$.
--
--   Differences from the source:
--   - encoding: a DAG $G=(V,E)$ with start $s$, target $t$ and parallel edges → `Graph` extends the published multigraph `Network` (an edge type with `tail`, `head`); `Acyclic` means no nonempty closed walk; a path is an edge list chained by `IsPathFrom`; reason: same instances: a finite graph has no closed walk exactly when it is a DAG, and in a DAG every walk is a path
--   - encoding: a finite graph and a finite label set $L$ → `[Fintype V] [Fintype E] [Fintype L]`, with `V E L : Type`; reason: finite data; every finite type is equivalent to one in `Type`
--   - reading: $L_e \subset L$ → `labels e : Finset L`, i.e. $L_e\subseteq L$; reason: with one label the labelled edges of the $m$-choice example (p.5) have $L_e=L$; the strict reading would exclude it
--   - reading: an algorithm or policy $ALG$ that determines at each node which edge to follow next, given the observed realizations so far, where $w_e$ is observed when the tail of $e$ is reached → an `OnlinePolicy` with a seed space $\Xi$ and seed law $\nu$: the decision reads $w$ only on edges leaving visited nodes; the seed is independent of the values (expectation under $\nu\otimes\mu$); the run is a label-feasible $s,t$-path for every seed and value vector; the run is cut off after $|V|$ steps; reason: the model of p.6; the algorithms of pp.8–12 are randomized, their coins drawn independently of everything else; an $s,t$-path of a DAG has fewer than $|V|$ edges
--   - reading: $\mathbb E(ALG)$, an expectation → an extra conjunct: the selected path is a random variable (`RunMeasurable`: each event $\{ALG\text{ selects }p\}$ is measurable); reason: an expectation presupposes a random variable; the conjunct only strengthens the conclusion
--   - encoding: $G_i$: nodes $V(P_i)$, the edges between them, and an artificial edge $e'=(u,v')$ with $w_{e'}=w_e$ for each edge $e=(u,v)$ with $u\in V(P_i)$, $v\notin V(P_i)$ → `focal G (P i)`: nodes $\{t\}\cup V(P_i)$; edges the edges $e$ of $G$ with $\mathrm{tail}(e)\in V(P_i)$, the artificial $e'$ being $e$ itself with head $v'$ (head $t$ if no node of $V(P_i)$ is reachable); values $w\circ$`Subtype.val`; labels copied; reason: the same graph whenever $P_i$ is an $s,t$-path and every node reaches $t$, which the hypotheses guarantee
--   - generalization: the algorithm of Theorem 3 on $G_i$ → every online policy on $G_i$ whose runs are feasible $s,t$-paths and random variables; reason: Theorem 3's policy is such a policy
--   - reading: "conditional on choosing $G_i$, $ALG$ gets as much value as the algorithm for a single path on $G_i$" → for every seed and every value vector, the value collected in $G$ is at least the value collected in $G_i$; reason: the simulation gives the inequality realization by realization; it implies the conditional statement because the choice of $G_i$ is independent of the values
--   - generalization: the standing assumptions at most $d$ labels per edge (Theorem 4), $c_\ell\ge1$ (p.7), and random values independent across source nodes (p.7) → not assumed: no $d$, no `CapPos`, no measure or independence on the values `W`; reason: the simulation is built seed by seed and value vector by value vector and uses only acyclicity, the cover and the parallel unlabelled edges; the paper's case is included
--   - encoding: a capacity $c_\ell\ge1$ for each label, with $|P\cap E(\ell)|\le c_\ell$ → `cap : L → ℕ` (natural-number capacities); reason: an edge count is an integer, so $|P\cap E(\ell)|\le c_\ell$ exactly when $|P\cap E(\ell)|\le\lfloor c_\ell\rfloor$, and $\lfloor c_\ell\rfloor\ge1$; same instances
-- source:
--   Cristi, Oren, Planning Against a Prophet: A Graph-Theoretic Framework for Making Sequential Decisions, arXiv:2406.13911v1, §4.1 Proof of Theorem 4, p.12, "That is, whenever the algorithm takes an edge that starts and ends in V(Pi) … ALG gets as much value as the algorithm for a single path on Gi"

import Mathlib
import Definitions.Def_PlanningProphet_FocalGraph
import Definitions.Def_PlanningProphet_OnlinePolicy

open scoped NNReal ENNReal
open MeasureTheory

universe u

namespace PlanningProphet

/-- **Running a `Gᵢ` policy in `G`** (Cristi–Oren, arXiv:2406.13911v1, §4.1, p.12).
"That is, whenever the algorithm takes an edge that starts and ends in `V(Pᵢ)`, it takes the same
edge in the original graph; and whenever it takes an artificial edge, it takes the corresponding
path in `G`. By the definition of `Gᵢ`, and because choosing `Gᵢ` is independent of the values,
we have that conditional on choosing `Gᵢ`, ALG gets as much value as the algorithm for a single
path on `Gᵢ`."

`G` is a DAG covered by the `s,t`-paths `P₁, …, P_k`, with parallel unlabelled edges. For every
online policy `π` on `Gᵢ` (seed space `Ξ`) whose run is always a label-feasible `s,t`-path of
`Gᵢ` and is a random variable for the values `W ∘ Subtype.val`, there is an online policy `π′` on
`G` with the same seed space whose run is always a label-feasible `s,t`-path of `G`, is a random
variable for the values `W`, and collects, for every seed `ξ` and every value vector `w`, at least
the value that `π` collects on `Gᵢ` under `w ∘ Subtype.val`. -/
theorem focal_simulation {V E L : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype L] [DecidableEq L] (G : Graph V E L) (hG : G.Acyclic) {k : ℕ}
    (P : Fin k → List E) (hP : G.CoveredBy P) (hpar : G.ParallelUnlabeled) (i : Fin k)
    {Ξ : Type u} [MeasurableSpace Ξ] {Ω : Type u} [MeasurableSpace Ω] (W : Ω → E → ℝ≥0)
    (π : OnlinePolicy (G.focal (P i)) Ξ) (hπ : π.IsFeasibleRun)
    (hπm : π.RunMeasurable (fun ω e => W ω e.1)) :
    ∃ π' : OnlinePolicy G Ξ, π'.IsFeasibleRun ∧ π'.RunMeasurable W ∧
      ∀ ξ w, π.algValue ξ (fun e => w e.1) ≤ π'.algValue ξ w := by sorry

end PlanningProphet
