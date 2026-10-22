-- Prove2me | Theorems.Thm_SidB_blowup_sidorenko
-- name    : SidB.blowup_sidorenko
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T21:32:11.39358+00:00
-- url     : https://prove2.me/theorems/10d60ad6-f165-4ae2-94ee-3e4ec11bee31
-- title:
--   Sidorenko's conjecture holds for a blow-up of every bipartite graph (Corollary 1.3)
-- statement:
--   Corollary 1.3 of the paper, the title result: for every bipartite graph H with bipartition A union B there is a positive integer p such that the blow-up H_A^p satisfies Sidorenko's conjecture; in the paper, p = |A|! always suffices. The blown-up right vertices have degrees p times the original degrees, and since C(|A|, r) C(r, k) divides |A|! r! for each k - equivalently, since C(|A|, k) C(|A|-k, r-k) divides the blown-up degree counts - the divisibility criterion of Theorem 1.1 applies to the blow-up. The L^p reading of the introduction: the statement says that for every bipartite graph the expectation of the rho-density functional to the power p bounds the edge density to the power p times the edge count, for the p furnished by the corollary; that is exactly the homomorphism Sidorenko inequality for the blow-up.
--
--   **Formalization Note** The goal is stated existentially over p; the paper's proof of Corollary 1.3 through the factorial blow-up is the proposed work of the goal, consuming the divisibility conjunct of the preceding milestone.
-- source:
--   D. Conlon, J. Lee, Sidorenko's conjecture for blow-ups, Discrete Anal. 2021:2 (2021), Introduction (Corollary 1.3, page 3), via Theorem 1.1.

import Mathlib
import Definitions.Def_SidB_graph
import Definitions.Def_SidB_hyper

namespace SidB

/-!  The goal (Corollary 1.3): Sidorenko's conjecture holds for a blow-up
of every bipartite graph. For every bipartite graph H there is a positive
integer p such that the blow-up of H relative to its left part satisfies
Sidorenko. In the paper p = |A|! always suffices: the degrees of the
blown-up right vertices are multiplied by p, so the divisibility conditions
of Theorem 1.1 hold for the blow-up with p = |A|!, and the L^p reading of
Corollary 1.3 - the expected rho-density to the power p against the edge
density to the power p times the edge count - is exactly the homomorphism
density of the blow-up. -/
theorem blowup_sidorenko {A B : Type} [Fintype A] [Fintype B] (H : Bigraph A B) :
    ∃ p : ℕ, SatisfiesSidorenko (H.blowUp p) := by sorry

end SidB
