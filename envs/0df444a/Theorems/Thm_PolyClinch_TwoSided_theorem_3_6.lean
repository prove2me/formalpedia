-- Prove2me | Theorems.Thm_PolyClinch_TwoSided_theorem_3_6
-- name    : PolyClinch.TwoSided.theorem_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:02.389369+00:00
-- url     : https://prove2.me/theorems/6628106b-5d8e-4c75-a162-a2661f1f480b
-- title:
--   Theorem 3.6, p. 12 — the clinching polytope P^i_{w,d} is a polymatroid and has a maximal vector (polynomial-time clauses omitted)
-- statement:
--   Let each $f_j$ be monotone submodular on $E_j$, and work in the extended market (with virtual buyers). Let $w\in P$ be a transaction vector, $d\in(\mathbb R_+\cup\{\infty\})^N$ a demand vector, and $i$ a buyer. Then there is a monotone submodular function $g$ on $E_i$ such that the clinching polytope of buyer $i$ is its polymatroid:
--   $$
--   P^i_{w,d}=\{\xi\in\mathbb R^{E_i}_+\mid P^i_{w,d}(\xi)=P^i_{w,d}(0)\}=P(g),
--   $$
--   and $P^i_{w,d}$ has a maximal vector.
--
--   This is what makes line 5 of Algorithm 2 well defined: a maximal clinching vector exists, and it can be found greedily.
--
--   **Formalization Note** The page also asserts that the value of $g$, and hence a maximal vector, can be computed in polynomial time; these complexity clauses are not stated. The page's proof (§5.1, explicit $g=h^i_{w,d}$ of (26)) uses only $w\in P$ and $d\ge0$, which are the hypotheses here; the theorem is therefore stated for every such pair, not only for states reached by the algorithm. Vectors on $E_i$ are vectors on all edges vanishing off $E_i$.
-- source:
--   Hirai & Sato, Polyhedral Clinching Auctions for Two-sided Markets, arXiv:1708.04881v2, p. 12, Theorem 3.6; proof in §5.1, pp. 20–23 (Theorem 5.2 (ii))

import Mathlib
import Definitions.Def_PolyClinch_TwoSided_Clinching

namespace PolyClinch.TwoSided

/-- Theorem 3.6 (Hirai–Sato p. 12), without the polynomial-time clauses. For a transaction vector
`w ∈ P` and a nonnegative demand vector `d` of the preprocessed market, the clinching polytope
`P^i_{w,d}` of buyer `i` is the polymatroid of a monotone submodular function on `E_i`, and it
has a maximal vector. -/
theorem theorem_3_6 {n m : ℕ} (E : Finset (Fin n × Fin m)) (I : PublicInfo E)
    (hf : ∀ j, IsMonoSubmodOn (edgesOfSeller E j) (I.f j))
    (w : ↥(extEdges E) → ℝ) (hw : w ∈ extP E I)
    (d : Fin (n + m) → WithTop ℝ) (hd : ∀ i, 0 ≤ d i) (i : Fin (n + m)) :
    (∃ g : Finset ↥(extEdges E) → ℝ, IsMonoSubmodOn (extEdgesOfBuyer E i) g ∧
      clinchingPolytope E I w d i =
        {ξ | ξ ∈ polymatroidOn (extEdgesOfBuyer E i) g ∧ ∀ e ∉ extEdgesOfBuyer E i, ξ e = 0}) ∧
      ∃ ξ, Maximal (· ∈ clinchingPolytope E I w d i) ξ := by sorry

end PolyClinch.TwoSided
