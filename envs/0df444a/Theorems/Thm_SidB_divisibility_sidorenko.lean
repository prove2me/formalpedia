-- Prove2me | Theorems.Thm_SidB_divisibility_sidorenko
-- name    : SidB.divisibility_sidorenko
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-21T21:31:47.597679+00:00
-- url     : https://prove2.me/theorems/03ab0a77-3ca8-473b-baed-2e4aefe03c61
-- title:
--   The divisibility and regular criteria for Sidorenko (Theorems 1.1 and 1.2)
-- statement:
--   The two main theorems of the paper's introduction. Theorem 1.1: let H be a bipartite graph with bipartition A union B, maximum right degree r, and, for each 1 <= k <= r, let d_k be the number of vertices of degree k in B. If C(|A|, r) C(r, k) divides d_k for each k, then H satisfies Sidorenko. Theorem 1.2: if every vertex of B has degree r and |B| is at least C(|A|, r), then H satisfies Sidorenko. The first proof applies the Hoelder trick (the milestone on Theorem 4.1): the divisibility hypothesis makes the weight vector alpha_k = d_k / C(|A|, k) integral with C(|A|-k, r-k) dividing alpha_k, so the weighted downset Sidorenko theorem applies. The second uses the second part of Theorem 4.1, the convexity of the power function, and the weak-norming property of the (|A|, r)-incidence graph. The two conclusions are packaged as the two conjuncts of the statement.
--
--   **Formalization Note** The two conjuncts are independent implications; the goal of the mission (Corollary 1.3) consumes the first through the blow-up with p = |A|!, where the divisibility conditions hold by the factorial identity recorded in the introduction of the paper.
-- source:
--   D. Conlon, J. Lee, Sidorenko's conjecture for blow-ups, Discrete Anal. 2021:2 (2021), Introduction (Theorems 1.1 and 1.2, pages 2-3), proved in Section 4 (pages 8-9).

import Mathlib
import Definitions.Def_SidB_graph
import Definitions.Def_SidB_hyper

namespace SidB

/-!  Milestone 7 (Theorems 1.1 and 1.2): the divisibility and regular
sides of the main theorem. First, if H is a bipartite graph with left part
A and maximum right degree r such that C(|A|, r) * C(r, k) divides d_k -
the number of right vertices of degree k - for each 1 <= k <= r, then H
satisfies Sidorenko. Second, if every right vertex of H has degree r and
|B| is at least C(|A|, r), then H satisfies Sidorenko. The first part
applies the Hoelder trick (milestone 2) to reduce to the weighted downset
Sidorenko theorem (milestone 6); the second part additionally uses the
convexity of the power function and the weak-norming property of the
(|A|, r)-incidence graph. -/
theorem divisibility_sidorenko {A B : Type} [Fintype A] [Fintype B] (H : Bigraph A B) :
    ((∀ k, 1 ≤ k → k ≤ H.maxDeg →
        (Fintype.card A).choose H.maxDeg * (H.maxDeg.choose k) ∣ H.degCount k) →
      SatisfiesSidorenko H) ∧
    ((∀ b : B, (H.nbr b).card = H.maxDeg) →
      (Fintype.card A).choose H.maxDeg ≤ Fintype.card B →
      SatisfiesSidorenko H) := by sorry

end SidB
