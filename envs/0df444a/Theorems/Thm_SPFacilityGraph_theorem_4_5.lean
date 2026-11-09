-- Prove2me | Theorems.Thm_SPFacilityGraph_theorem_4_5
-- name    : SPFacilityGraph.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:02:09.855209+00:00
-- url     : https://prove2.me/theorems/7da35031-5de6-43ae-941d-2fb381d15d9a
-- title:
--   Theorem 4.5 — locality of strong strategyproofness
-- statement:
--   Let $G$ be a straight-edge metric graph, $n$ the number of agents, and let $\mathcal U$ be a finite family of closed convex polytopes in $(\mathbb R^k)^n \times \mathbb R^k$ covering $G^n \times G$. Let $C(\boldsymbol x, t)$ be any real-valued cost function on $G^n \times G$, for example the expected-cost function $C_M$ of a mechanism. Then $C$ satisfies all strong-strategyproofness constraints of Definition 4.4,
--   $$
--   d_G(t,z) = d_G(t,y) + d_G(y,z) \ \Longrightarrow\ C\big((y, \boldsymbol x_{-i}), t\big) \le C\big((z, \boldsymbol x_{-i}), t\big),
--   $$
--   if and only if it satisfies those constraints for which the two points $((y, \boldsymbol x_{-i}), t)$ and $((z, \boldsymbol x_{-i}), t)$ lie in a common cell $U \in \mathcal U$.
--
--   Locality reduces SSP to comparisons inside individual cells, where expected costs have polynomial formulas; it is the step that turns SSP into finitely many linear constraints and that proves deterministic attributions SSP.
--
--   **Formalization Note** Cells are convex hulls of finite point sets. The other reports are a full profile whose $i$-th entry is overwritten.
--
--   Differences from the source:
--   - generalization: the expected-cost function C_M of a mechanism M → any function C : Gⁿ × G → ℝ; reason: the proof "uses only the values of C_M at shared endpoints and requires no continuity assumption on M" (p.34); C_M is such a function
--   - generalization: U a finite subdivision of Gⁿ × G into closed convex polytopes (cells meeting in common faces) → 𝒰 any finite family of polytopes conv P covering Gⁿ × G; reason: a subdivision is such a cover, and Lemma I.1 needs only a cover
--   - generalization: n ≥ 2 agents (Section 2.2) → any n ∈ ℕ; reason: the statement and its proof do not use n ≥ 2
--   - encoding: a graph: a connected compact subset of R^k (k a positive integer), a finite union of edges with distinct endpoints meeting only at common endpoints, at least one edge, every edge a straight segment (standing assumption of Section 3.2) → MetricGraph k: a nonempty Finset of ordered endpoint pairs (a, b), a ≠ b, edge = segment ℝ a b, two distinct edges intersect only in common endpoints, union connected; k ∈ ℕ; reason: the straight-edge assumption is the paper's standing assumption for Theorem 7.2; compactness, positive finite length and no self-intersection are automatic for finitely many straight segments; k = 0 admits no edge with distinct endpoints, so the instances are the same
--   - encoding: d_G(x, y) = min over paths (minimal connected subsets) of their length → MetricGraph.dist: infimum over finite walks x = p_0, …, p_m = y with consecutive points on a common edge segment of Σ‖p_j − p_{j−1}‖; reason: on a straight-edge graph every path is traced by such a walk of equal length and every walk contains a path of no greater length; same value
--   - encoding: agents N = {1, …, n} → Fin n (0-based); reason: relabelling
-- source:
--   Rogowski–Dziubiński, Search and Verification for Strategyproof Facility Location on Metric Graphs, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Theorem 4.5, p.12 (restated with proof, Appendix I.1, pp.33–34)

import Mathlib
import Definitions.Def_SPFacilityGraph_IsSSPCost
import Definitions.Def_SPFacilityGraph_MetricGraph_embed

set_option autoImplicit false

namespace SPFacilityGraph

/-- Theorem 4.5 (locality of SSP) (Rogowski–Dziubiński, *Search and Verification for Strategyproof Facility Location on Metric Graphs*, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Theorem 4.5, p.12; restated with proof pp.33–34).

Let `𝒰` be a finite family of closed convex polytopes covering `Gⁿ × G ⊆ (ℝ^k)ⁿ × ℝ^k`. A cost
function `C(𝒙, t)` satisfies all SSP constraints of Definition 4.4 if and only if it satisfies
those constraints for which the two points `((y, 𝒙₋ᵢ), t)` and `((z, 𝒙₋ᵢ), t)` lie in a common
cell `U ∈ 𝒰`.

**Formalization Note** The paper states this for the expected-cost function `C_M` of a mechanism
and a finite subdivision of `Gⁿ × G`; here `C` is any real function on `Gⁿ × G` (the proof uses
only the values of `C_M` at shared endpoints, p.34) and `𝒰` is any finite cover by polytopes
`conv P` (a subdivision is such a cover; cells may extend beyond `Gⁿ × G`). -/
theorem theorem_4_5 {k n : ℕ} (G : MetricGraph k) (C : Profile G n → G.Pt → ℝ)
    (𝒰 : Finset (Finset ((Fin n → EuclideanSpace ℝ (Fin k)) × EuclideanSpace ℝ (Fin k))))
    (hcover : ∀ (x : Profile G n) (t : G.Pt), (G.embed x, (t : EuclideanSpace ℝ (Fin k))) ∈
      ⋃ P ∈ 𝒰, convexHull ℝ (P : Set ((Fin n → EuclideanSpace ℝ (Fin k)) × EuclideanSpace ℝ (Fin k)))) :
    IsSSPCost G C ↔
      ∀ (i : Fin n) (t : G.Pt) (x : Profile G n) (y z : G.Pt),
        G.dist t z = G.dist t y + G.dist y z →
        (∃ P ∈ 𝒰,
          (G.embed (Function.update x i y), (t : EuclideanSpace ℝ (Fin k))) ∈
            convexHull ℝ (P : Set ((Fin n → EuclideanSpace ℝ (Fin k)) × EuclideanSpace ℝ (Fin k))) ∧
          (G.embed (Function.update x i z), (t : EuclideanSpace ℝ (Fin k))) ∈
            convexHull ℝ (P : Set ((Fin n → EuclideanSpace ℝ (Fin k)) × EuclideanSpace ℝ (Fin k)))) →
        C (Function.update x i y) t ≤ C (Function.update x i z) t := by sorry

end SPFacilityGraph
