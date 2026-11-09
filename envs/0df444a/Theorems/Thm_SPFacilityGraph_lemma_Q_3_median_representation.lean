-- Prove2me | Theorems.Thm_SPFacilityGraph_lemma_Q_3_median_representation
-- name    : SPFacilityGraph.lemma_Q_3_median_representation
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:59:18.78197+00:00
-- url     : https://prove2.me/theorems/baf87151-13d8-4687-b5d6-c359427b77a5
-- title:
--   Proof of Lemma Q.3, (Q.1)–(Q.2) — SP onto mechanisms on a segment are generalized median voter schemes
-- statement:
--   Let $G = [0, L]$ with $L > 0$ and $n \ge 2$, and let $M : G^n \to G$ be a deterministic strategyproof onto mechanism. Then $M$ is a **generalized median voter scheme**: there are thresholds $t_S \in [0, L]$, indexed by coalitions $S \subseteq N$, such that
--   $$
--   t_\emptyset = 0, \qquad t_N = L, \qquad t_S \le t_U \ \text{ for all } S \subseteq U \subseteq N, \tag{Q.1}
--   $$
--   and
--   $$
--   M(\boldsymbol x) = \max_{S \subseteq N} \min\big(\{x_i : i \in S\} \cup \{t_S\}\big) \qquad \text{for all } \boldsymbol x \in G^n. \tag{Q.2}
--   $$
--
--   The paper takes this representation from Schummer and Vohra [SV02, Section 3, Proposition 1] in the proof of Lemma Q.3; its thresholds supply the constant selectors and its comparisons the triangulation of the segment case.
--
--   **Formalization Note** The segment is any metric graph whose point set is a segment $[p, q] \subseteq \mathbb R^k$, possibly subdivided into several edges; a point $x$ is identified with its arclength coordinate $\|x - p\| \in [0, L]$, $L = \|q - p\|$, and (Q.2) is stated for these coordinates.
--
--   Differences from the source:
--   - generalization: G = [0, L] ⊆ ℝ with L > 0 → any MetricGraph k whose carrier is a segment [p, q] ⊆ ℝ^k (any subdivision into edges), arclength coordinate ‖x − p‖ and L = ‖q − p‖; the hypothesis L > 0 is not stated; reason: [0, L] with any set of vertices is the case k = 1, p = 0, q = L; L > 0 follows from the graph having an edge with distinct endpoints, so the dropped hypothesis excludes nothing
--   - encoding: d_G(x, y) = min over paths (minimal connected subsets) of their length → MetricGraph.dist: infimum over finite walks x = p_0, …, p_m = y with consecutive points on a common edge segment of Σ‖p_j − p_{j−1}‖; reason: on a straight-edge graph every path is traced by such a walk of equal length and every walk contains a path of no greater length; same value
--   - encoding: max over S ⊆ N and min over {x_i : i ∈ S} ∪ {t_S} → Finset.sup' over all S : Finset (Fin n) of Finset.min' of insert (t S) (image of the coordinates over S); reason: finite nonempty max and min
--   - encoding: a deterministic mechanism M : Gⁿ → Δ(G) with degenerate lotteries, cost(δ_y, x) = d_G(y, x) → M : Profile G n → G.Pt, cost d_G(M(𝒙), x); reason: the paper identifies each point with its point mass (p.4); same mechanisms and costs
--   - encoding: onto: every location of G is an output at some profile → Function.Surjective M; reason: same condition
--   - encoding: agents N = {1, …, n} → Fin n (0-based); reason: relabelling
-- source:
--   Rogowski–Dziubiński, Search and Verification for Strategyproof Facility Location on Metric Graphs, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), proof of Lemma Q.3, (Q.1)–(Q.2), p.50 (from [SV02, Section 3, Proposition 1])

import Mathlib
import Definitions.Def_SPFacilityGraph_IsSP

set_option autoImplicit false

namespace SPFacilityGraph

/-- Generalized median representation on a line segment (Rogowski–Dziubiński, *Search and Verification for Strategyproof Facility Location on Metric Graphs*, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), proof of Lemma Q.3,
(Q.1)–(Q.2), p.50; the paper takes it from Schummer–Vohra [SV02, Section 3, Proposition 1]).

Let `G = [0, L]`, `L > 0`, and `n ≥ 2`. Every deterministic SP onto mechanism `M : Gⁿ → G` is a
generalized median voter scheme: there are thresholds `t_S ∈ [0, L]`, `S ⊆ N`, with
`t_∅ = 0`, `t_N = L`, `t_S ≤ t_U` for `S ⊆ U` (Q.1), and
`M(𝒙) = max_{S ⊆ N} min ({xᵢ : i ∈ S} ∪ {t_S})` for all `𝒙` (Q.2).

**Formalization Note** Generalized from `[0, L] ⊆ ℝ` to every metric graph whose carrier is a
segment `[p, q] ⊆ ℝ^k` (any subdivision into edges): a point `x` has arclength coordinate
`‖x − p‖ ∈ [0, L]`, `L = ‖q − p‖` (`L > 0` because the graph has an edge with distinct
endpoints). Thresholds are real numbers in `[0, L]` and (Q.2) is stated for coordinates; the
max over the finite set of coalitions and the min over the nonempty finite set
`{t_S} ∪ {xᵢ : i ∈ S}` are `Finset.sup'` / `Finset.min'`. Agents are `Fin n`. -/
theorem lemma_Q_3_median_representation {k n : ℕ} (hn : 2 ≤ n) (G : MetricGraph k)
    (p q : EuclideanSpace ℝ (Fin k)) (hG : G.carrier = segment ℝ p q)
    (M : Profile G n → G.Pt) (hSP : IsSP G M) (hM : Function.Surjective M) :
    ∃ t : Finset (Fin n) → ℝ, (∀ S, 0 ≤ t S ∧ t S ≤ ‖q - p‖) ∧ t ∅ = 0 ∧
      t Finset.univ = ‖q - p‖ ∧ (∀ S U, S ⊆ U → t S ≤ t U) ∧
      ∀ x : Profile G n, ‖((M x : G.Pt) : EuclideanSpace ℝ (Fin k)) - p‖ =
        Finset.univ.sup' Finset.univ_nonempty (fun S : Finset (Fin n) =>
          (insert (t S) (S.image fun i => ‖((x i : G.Pt) : EuclideanSpace ℝ (Fin k)) - p‖)).min'
            (Finset.insert_nonempty _ _)) := by sorry

end SPFacilityGraph
