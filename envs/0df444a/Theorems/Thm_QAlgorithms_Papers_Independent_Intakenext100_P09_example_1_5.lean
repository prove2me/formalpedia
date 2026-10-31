-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P09_example_1_5
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P09.example_1_5
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:11:04.389164+00:00
-- url     : https://prove2.me/theorems/8c519725-f6e2-47f3-9c11-fb411f7d092d
-- title:
--   Example 1.5
-- statement:
--   Let $G$ be a topological group and $U\subseteq G$ an open set containing the identity. Define $\mathcal U_U=\{gU:g\in G\}$. Then $\mathcal U_U$ is an invariant open cover of $G$. In each degree $n\ge0$, let
--
--   $$\mathcal U_U[n]=\bigcup_{g\in G}(gU)^{n+1}.$$
--
--   These sets are open and invariant under simultaneous left translation. Every coordinate-selection map, including every face and degeneracy map, sends the corresponding set into the set in its target degree. Thus they form an open simplicial $G$-subspace of $G^{\bullet+1}$. Invariance refers to the translated family; its individual members need not be invariant.
-- source:
--   A Spectral Sequence Connecting Continuous With Locally Continuous Group Cohomology, arXiv:1110.0994v1, PDF p. 3, Example 1.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P09

universe u v w

/-- PDF p. 3, Example 1.5: translated identity neighborhoods cover the group,
are invariant as a family, and give an open simplicial invariant subspace.
All coordinate maps include faces and degeneracies. -/
theorem example_1_5 {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Set G) (hU : IsOpen U) (h1 : (1 : G) ∈ U) :
    ∃ C : OpenCover G, C.sets = translatedFamily U ∧ InvariantCover G C ∧
      (∀ n : ℕ, IsOpen (coverDiagonal C n)) ∧
      (∀ (n : ℕ) (x : Fin (n + 1) → G), x ∈ coverDiagonal C n →
        ∀ g : G, (fun i => g * x i) ∈ coverDiagonal C n) ∧
      (∀ (n m : ℕ) (a : Fin (m + 1) → Fin (n + 1)) (x : Fin (n + 1) → G),
        x ∈ coverDiagonal C n → x ∘ a ∈ coverDiagonal C m) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P09

end
