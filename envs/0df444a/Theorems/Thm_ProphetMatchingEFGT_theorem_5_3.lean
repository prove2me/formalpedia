-- Prove2me | Theorems.Thm_ProphetMatchingEFGT_theorem_5_3
-- name    : ProphetMatchingEFGT.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:51:33.509152+00:00
-- url     : https://prove2.me/theorems/d33f7d5f-c110-4b39-a97d-e53092762494
-- title:
--   Theorem 5.3 — a $0.337$-OCRS for general graphs with edge arrivals
-- statement:
--   Let $G=(V,E)$ be a finite simple graph (not necessarily bipartite) and $x\in\mathcal F_M$. Let each edge be realized independently with probability $x_e$. There is an online contention resolution scheme, which does not know the arrival order, such that for every arrival order $\sigma$ and every edge $e$
--   $$\Pr[e\in I,\ e\in R_e]\ \ge\ 0.337\cdot x_e,$$
--   i.e. $\Pr[e\in I\mid e\in R_e]\ge0.337$ whenever $x_e>0$, where $I$ is the selected matching.
--
--   Through Theorem 2.3 and §3 it gives the $0.337$-competitive prophet inequality for edge arrivals.
--
--   Differences from the source:
--   - reading: 'a 0.337-OCRS for general graphs with edge arrivals' → for every finite simple graph and every x ∈ FM, one OCRS that is 0.337-selectable under every order; reason: §5, p.12: R is described by x ∈ [0,1]^E and it suffices to construct a c-OCRS for every x ∈ FM; the OCRS faces an oblivious adversary
--   - encoding: Pr[e ∈ I | e ∈ R_e] ≥ c → product form Pr[A, B] ≥ c·Pr[B] (or the corresponding product of probabilities); reason: the conditional probability is undefined on null events (slip 6); equal where it is defined
--   - encoding: 0.337 → 337/1000; reason: the literal constant
--   - encoding: an online selection algorithm → a structure with a probability space and a measurable decision from the history of edges and realization bits; reason: the decision may use exactly what Definition 2.1 allows
--   - reading: a graph G = (V, E) (not necessarily bipartite) whose edges are written (uv) (§3, p.9) → a Mathlib SimpleGraph on a finite vertex type: no loops, at most one edge between two vertices; reason: the notation (uv), x_uv and FM's Σ_u y(uv) (p.10) presume one edge per pair of vertices, and (11), (13) use that (uv) is the only u–v edge
-- source:
--   Ezra–Feldman–Gravin–Tang, Online Stochastic Max-Weight Matching: prophet inequality for vertex and edge arrival models, arXiv:2002.09807v2, §5.2, Theorem 5.3, p. 14 (with §5 p. 12: 'it suffices to construct a c-OCRS for every x ∈ FM')

import Mathlib
import Definitions.Def_ProphetMatchingEFGT_EdgeArrival

namespace ProphetMatchingEFGT

/-- **Theorem 5.3, p. 14: a 0.337-OCRS for general graphs with edge arrivals.**
Ezra–Feldman–Gravin–Tang, arXiv:2002.09807v2, Theorem 5.3, p. 14: "There is a 0.337-OCRS for general
graphs with edge arrivals."

**Formalization Note.** For every finite simple graph `G` and every `x ∈ FM` (§5, p. 12: "it suffices
to construct a c-OCRS for every `x ∈ FM`") there is one OCRS, which does not know the arrival order,
selecting every edge `e` with `Pr[e ∈ I, e ∈ R_e] ≥ 0.337 · x_e` under every order, where `R_e = {e}`
independently with probability `x_e`. The constant is the literal `337/1000`. -/
theorem theorem_5_3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : Edge G → ℝ) (hx : InFM G x) :
    ∃ A : EdgeOCRS G, A.IsSelectable x (337 / 1000) := by sorry

end ProphetMatchingEFGT
