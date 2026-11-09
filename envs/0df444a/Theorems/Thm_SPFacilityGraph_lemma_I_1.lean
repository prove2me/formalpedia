-- Prove2me | Theorems.Thm_SPFacilityGraph_lemma_I_1
-- name    : SPFacilityGraph.lemma_I_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:47:04.348476+00:00
-- url     : https://prove2.me/theorems/89b1a5e2-8081-41fe-9720-94c4aeb1999b
-- title:
--   Lemma I.1 — partitioning a polygonal path among covering polytopes
-- statement:
--   Let $V$ be a real normed space (for instance $\mathbb R^k$) and let $\mathcal U$ be a finite family of closed convex polytopes $\operatorname{conv} P$, $P \subseteq V$ finite. Let $\gamma : [0,1] \to V$ be a continuous piecewise-affine path with finitely many affine pieces, that is, there are $0 = r_0 < r_1 < \dots < r_p = 1$ and $a_j, b_j \in V$ with $\gamma(s) = a_j + s\, b_j$ on $[r_{j-1}, r_j]$, and suppose every point $\gamma(s)$, $s \in [0,1]$, lies in some member of $\mathcal U$. Then there are
--   $$
--   0 = s_0 < s_1 < \dots < s_m = 1
--   $$
--   and $U_1, \dots, U_m \in \mathcal U$ such that
--   $$
--   \gamma([s_{j-1}, s_j]) \subseteq U_j \qquad \text{for all } j \in \{1, \dots, m\}.
--   $$
--
--   The lemma is the path-splitting step of the locality theorem for strong strategyproofness: an outward movement of a report is cut into finitely many portions each lying in one cell.
--
--   **Formalization Note** $\gamma$ is a function on $\mathbb R$ whose values outside $[0,1]$ play no role; the covered set $Y$ of the paper is left implicit. Indices of the partition are 0-based.
--
--   Differences from the source:
--   - generalization: Y ⊆ ℝ^k for a nonnegative integer k → any real normed space V; reason: the proof uses only that a polytope conv P is closed and convex and that γ is affine on each piece; ℝ^k is a real normed space
--   - encoding: Y ⊆ ℝ^k covered by 𝒰 and γ : [0, 1] → Y → γ : ℝ → V with γ(s) ∈ ⋃_{P∈𝒰} conv P for s ∈ [0, 1], continuous on [0, 1]; reason: Y can be taken to be the covered set; values outside [0, 1] are unused
--   - encoding: piecewise affine with finitely many affine pieces → breakpoints 0 = r_0 < … < r_p = 1 with γ(s) = a + s·b on each [r_{j−1}, r_j]; reason: an affine map of an interval into V has exactly this form
--   - encoding: U_1, …, U_m indexed by j ∈ {1, …, m} → j : Fin m with interval [s_j, s_{j+1}]; reason: 0-based relabelling
-- source:
--   Rogowski–Dziubiński, Search and Verification for Strategyproof Facility Location on Metric Graphs, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Lemma I.1, (I.1)–(I.2), p.33

import Mathlib

set_option autoImplicit false

namespace SPFacilityGraph

/-- Lemma I.1 (partitioning a polygonal path among covering polytopes) (Rogowski–Dziubiński, *Search and Verification for Strategyproof Facility Location on Metric Graphs*, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Lemma I.1,
(I.1)–(I.2), p.33).

Let `𝒰` be a finite family of closed convex polytopes `conv P` (`P` a finite point set) covering
the image of a continuous piecewise-affine path `γ : [0, 1] → V` with finitely many affine
pieces. Then there are `0 = s₀ < s₁ < ⋯ < s_m = 1` and polytopes `U₁, …, U_m ∈ 𝒰` with
`γ([s_{j−1}, s_j]) ⊆ U_j` for all `j`.

**Formalization Note** The paper's `ℝ^k` is generalized to any real normed space `V`. The set
`Y` covered by `𝒰` is left implicit: the hypothesis is that every point `γ(s)`, `s ∈ [0, 1]`,
lies in some `conv P`, `P ∈ 𝒰`. "Piecewise affine with finitely many pieces": breakpoints
`0 = r₀ < ⋯ < r_p = 1` with `γ(s) = a + s·b` on each `[r_{j−1}, r_j]`. `γ` is a function on
`ℝ` whose values outside `[0, 1]` are irrelevant. Indices are 0-based (`j : Fin m` stands for
the paper's `j + 1`). -/
theorem lemma_I_1 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (𝒰 : Finset (Finset V)) (γ : ℝ → V)
    (hcover : ∀ s ∈ Set.Icc (0 : ℝ) 1, γ s ∈ ⋃ P ∈ 𝒰, convexHull ℝ (P : Set V))
    (hcont : ContinuousOn γ (Set.Icc 0 1))
    (hpw : ∃ (p : ℕ) (r : Fin (p + 1) → ℝ), StrictMono r ∧ r 0 = 0 ∧ r (Fin.last p) = 1 ∧
      ∀ j : Fin p, ∃ a b : V, ∀ s ∈ Set.Icc (r j.castSucc) (r j.succ), γ s = a + s • b) :
    ∃ (m : ℕ) (s : Fin (m + 1) → ℝ), StrictMono s ∧ s 0 = 0 ∧ s (Fin.last m) = 1 ∧
      ∀ j : Fin m, ∃ P ∈ 𝒰, γ '' Set.Icc (s j.castSucc) (s j.succ) ⊆ convexHull ℝ (P : Set V) := by sorry

end SPFacilityGraph
