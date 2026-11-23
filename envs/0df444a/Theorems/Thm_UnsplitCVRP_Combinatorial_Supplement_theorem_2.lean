-- Prove2me | Theorems.Thm_UnsplitCVRP_Combinatorial_Supplement_theorem_2
-- name    : UnsplitCVRP.Combinatorial.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:42:02.113414+00:00
-- url     : https://prove2.me/theorems/80c7c5c0-ea8d-4eb7-b30b-2a1b8c846b63
-- title:
--   Theorem 2, p. 2 — Algorithm 2 is a $(\ln 2+\alpha+\frac1{1-\delta})$-approximation in expectation
-- statement:
--   Consider an instance of the CVRP with unsplittable demands: clients $V$, depot $r$, metric costs $c$, demands $d_v\in(0,1]$ and vehicle capacity $1$. Fix $0<\delta<1$, call a client big if $d_v>\delta$, and let $x^*$ be an optimal solution of the Configuration-LP over the set $\mathcal J$ of feasible big-client tours. Let $\alpha$ be a TSP approximation ratio: for every set $U$ of clients, $\mathrm{tour}(U)$ is a tour through $r$ and exactly the clients of $U$ of cost at most $\alpha$ times the optimal TSP tour on $U$.
--
--   Algorithm 2 keeps each $T\in\mathcal J$ independently with probability $\min\{1,\gamma x^*_T\}$, $\gamma=\ln2$, takes the TSP tour $\mathcal A=\mathrm{tour}(V\setminus V(\mathcal T))$ on the clients the kept tours miss, splits it optimally into consecutive feasible tours (δ-tank step), and returns the kept tours together with these. Then
--
--   1. for every outcome $\mathcal T$ there is a feasible solution of cost at most the cost of the returned tours, and
--   2. for every feasible solution $R$,
--   $$\mathbb E\big[c(\mathcal T\cup\mathcal T')\big]\ \le\ \Big(\ln 2+\alpha+\frac{1}{1-\delta}\Big)\cdot c(R).$$
--
--   In particular the expected cost is at most $(\ln2+\alpha+\frac1{1-\delta})\cdot\mathrm{opt}$. This improves the ratio $\alpha+2$ of the classical tour-partitioning method once $\delta$ is small, and it is the algorithm combined with Blauth–Traub–Vygen in Theorem 14.
--
--   **Formalization Note** The expectation is the finite sum over subcollections of $\mathcal J$ weighted by the independent rounding law. The cost of the returned tours is the sum of the kept tours' costs plus the optimal consecutive split of $\mathcal A$; shortcutting repeated clients (p. 9) can only lower it, which is clause 1. Comparing with every feasible solution is equivalent to comparing with opt. The running time $n^{O(1/\delta)}$ has no explicit constant and is not formalized, as in the published Lemma 7.
--
--   Differences from the source:
--   - reading: "for any δ > 0" → 0 < δ < 1; reason: at δ = 1 the ratio 1/(1−δ) is undefined and for δ > 1 it is negative, so the printed claim has content only for δ < 1; this is wider than §4's standing range (0, 1/2] (p. 9), and for δ ∈ (1/2, 1) the bound follows from Lemma 7 at threshold 0 together with 2 ≤ 1/(1−δ)
--   - reading: "an approximation algorithm with ratio ρ" for a randomized algorithm → the expected cost of Algorithm 2's output is at most ρ times every feasible solution's cost, and every outcome is (at least as costly as) a feasible solution; reason: this is what display (10) proves
--   - reading: running time n^{O(1/δ)} → not stated; reason: an O-bound with no constant is not a proposition about this model; the published Lemma 7 treats O(n²) the same way
--   - encoding: an α-approximate TSP tour on r ∪ (V \ V(𝒯)) → a function tour(U), for every client set U, with cost ≤ α · tspOn U; reason: the uncovered set is random, so the tour is chosen per outcome
--   - encoding: "apply the δ-tank lemma to 𝒜" → the optimal consecutive split bestSplit of 𝒜; reason: p. 7 computes the optimal consecutive partition by dynamic programming, as in the published alg1Cost
--   - encoding: shortcut repeated clients → some feasible solution costs at most the returned tours' cost; reason: shortcutting only lowers the cost in a metric
--   - generalization: α a TSP approximation ratio (α ≥ 1) → α any real number; reason: the tour hypotheses carry all the information about α, and the source's case α ≥ 1 is an instance
-- source:
--   Friggstad, Mousavi, Rahgoshay, Salavatipour, Improved Approximations for CVRP with Unsplittable Demands, arXiv:2111.08138v1, p. 2, Theorem 2 (Algorithm 2 and proof §4–§4.1, pp. 9–10, displays (8)–(10))

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_UnsplitCVRP_Combinatorial_Setting
import Definitions.Def_UnsplitCVRP_Combinatorial_Supplement_ConfigLP

namespace UnsplitCVRP.Combinatorial.Supplement

/-- Theorem 2, p. 2 (proof §4.1, pp. 9–10): every outcome of Algorithm 2 yields a feasible
solution, and its expected cost is at most `(ln 2 + α + 1/(1-δ))` times every feasible
solution's cost. -/
theorem theorem_2 {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hc : SupplyChainTheory.VRPMetric c) (d : Fin (n + 1) → ℝ)
    (hd : Demands d) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (α : ℝ)
    (xstar : List (Fin (n + 1)) → ℝ) (hx : IsConfigOptimal c d δ xstar)
    (tour : Finset (Fin (n + 1)) → List (Fin (n + 1)))
    (htour : ∀ U ⊆ clients n, IsTourOn U (tour U))
    (hctour : ∀ U ⊆ clients n, SupplyChainTheory.routeCost c (tour U) ≤ α * tspOn c U) :
    (∀ S ∈ (configTours d δ).powerset, ∃ R, IsSolution d R ∧
      SupplyChainTheory.solutionCost c R ≤ alg2Cost c d tour S) ∧
    ∀ R, IsSolution d R →
      expect d δ (Real.log 2) xstar (alg2Cost c d tour) ≤
        (Real.log 2 + α + 1 / (1 - δ)) * SupplyChainTheory.solutionCost c R := by sorry

end UnsplitCVRP.Combinatorial.Supplement
