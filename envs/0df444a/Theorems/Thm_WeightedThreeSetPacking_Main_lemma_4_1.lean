-- Prove2me | Theorems.Thm_WeightedThreeSetPacking_Main_lemma_4_1
-- name    : WeightedThreeSetPacking.Main.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:10.202412+00:00
-- url     : https://prove2.me/theorems/5f8f1233-9f2a-492f-a43c-a86c96637fa1
-- title:
--   Lemma 4.1 — Covering projection and residual gain (Tong and Xu, arXiv:2610.10036v1, p. 12)
-- statement:
--   Under the standing setting of Tong and Xu, arXiv:2610.10036v1, Lemma 4.1, p. 12, use the inclusive neighborhoods, claws and exact parameters defined above.
--
--   For a finite weight-preserving $M$-sheet graph cover $\varpi$ of the graph on the two packings, there exists a maximum-neighbor center assignment on the lift with all the following properties.
--
--   1. For each lifted center $\widetilde v$, projection is a weight-preserving bijection from its claw onto $C_{\varpi(\widetilde v)}$.
--   2. The image of its inclusive claw neighborhood is exactly the original claw neighborhood. Its neighborhood weight is at least the original weight, and $\widetilde g_{\widetilde v}\le g_{\varpi(\widetilde v)}$.
--   3. For every $\widetilde o\in\widetilde O\setminus\widetilde A$, projection bijects graph neighborhoods into the corresponding original $A$-neighborhood. There are at most three such neighbors and at most two secondary blockers.
--
--   For every $\widetilde J\subseteq\widetilde A$, $$\sum_{\widetilde v\in\widetilde J}\widetilde g_{\widetilde v}\le M G(A,O).$$
--
--   This result provides the corresponding source statement in the dependency chain for the full approximation theorem.
--
--   Differences from the source:
--   - generalization: Positive rational set weights, an optimum packing O, and its rank-three conflict graph (or an analysis lift). → Positive real weights on A∪O, independent O, and finite graphs with the inherited two-sided inclusive degree bounds and maximum-neighbor assignment.; reason: These inequalities use positivity, independence and the rank-three degree bounds; every source instance and its weight-preserving lift satisfies these assumptions.
--   - encoding: Finite set families, inclusive neighborhoods, witnessed exchange multiarcs and finite sums. → Finite carrier types and Finsets, with one triple per witnessed arc and inclusive neighborhoods.; reason: This preserves common vertices, distinct-neighbor sums and incidence multiplicities.
--   - generalization: The weight-preserving finite cover produced by Arkin–Hassin duplication and crossing. → Every weight-preserving finite graph cover with the same sheet and membership properties.; reason: The proof of all projection clauses uses local bijectivity, sheet count and weight preservation, not the origin or girth of the cover.
--   - generalization: A is the Phase I output in the source standing setting. → Any A with the stated positivity, independent comparison packing, neighborhood degrees and maximum-neighbor assignment; no square local optimality assumption.; reason: These projection, graph-structure and repair statements do not use the local optimality or improving path of Phase I.
-- source:
--   Tong and Xu, arXiv:2610.10036v1, Lemma 4.1, p. 12; https://arxiv.org/abs/2610.10036v1

import Definitions.Def_WeightedThreeSetPacking_Main_Cover

namespace WeightedThreeSetPacking.Main

open scoped BigOperators

/-- Tong and Xu, arXiv:2610.10036v1, Lemma 4.1, p. 12. -/
theorem lemma_4_1 {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (D : Analysis V) (E : Analysis W) (hvalid : ValidAnalysis D)
    (p : W → V) (M : ℕ) (hcover : SheetCover D E p M) :
    ∃ pi : W → W, let L := withCenter E pi
      (∀ o ∈ L.O, pi o ∈ neighbors L {o} L.A ∧
        ∀ v ∈ neighbors L {o} L.A, L.w v ≤ L.w (pi o)) ∧
      (∀ v ∈ L.A,
        Set.BijOn p (claw L v : Set W) (claw D (p v) : Set V) ∧
        (∀ o ∈ claw L v, L.w o = D.w (p o)) ∧
        (neighbors L (claw L v) L.A).image p = neighbors D (claw D (p v)) D.A ∧
        mass D (neighbors D (claw D (p v)) D.A) ≤
          mass L (neighbors L (claw L v) L.A) ∧
        residual L v ≤ residual D (p v)) ∧
      (∀ o ∈ L.O \ L.A,
        Set.BijOn p {v | v ∈ L.A ∧ L.graph.Adj o v}
          {v | v ∈ D.A ∧ D.graph.Adj (p o) v} ∧
        (neighbors L {o} L.A).card ≤ 3 ∧
        (neighbors L {o} (L.A \ {pi o})).card ≤ 2) ∧
      (∀ J ⊆ L.A, (∑ v ∈ J, residual L v) ≤ (M : ℝ) * residualTotal D) := by sorry

end WeightedThreeSetPacking.Main
