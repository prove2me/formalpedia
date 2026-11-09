-- Prove2me | Theorems.Thm_TenChallenges_sidorenko_sum
-- name    : TenChallenges.sidorenko_sum
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T03:35:04.082172+00:00
-- url     : https://prove2.me/theorems/89fec3ed-cc71-447a-b52f-6ca38f1ecb06
-- title:
--   Sidorenko's Inequality Is Closed under Disjoint Union
-- statement:
--   For finite graphs H1, H2, and G, if Sidorenko's inequality holds for both H1 and H2 against G, it also holds for their disjoint union against G. Homomorphism densities multiply, while the numbers of edges add.
-- source:
--   Ten Challenges in Combinatorics, Challenge 4; structural supporting lemma. https://tenchallenges.github.io/ten-challenges/

import Definitions.Def_TenChallenges_Challenge_04
import Mathlib.Combinatorics.SimpleGraph.Sum

namespace TenChallenges
open SimpleGraph
theorem sidorenko_sum {W₁ W₂ V : Type*} [Fintype W₁] [Fintype W₂] [Fintype V]
    (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂) (G : SimpleGraph V)
    (h₁ : SidorenkoFor H₁ G) (h₂ : SidorenkoFor H₂ G) :
    SidorenkoFor (H₁ ⊕g H₂) G := by sorry
end TenChallenges
