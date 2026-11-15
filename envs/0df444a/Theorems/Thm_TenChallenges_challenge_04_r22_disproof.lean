-- Prove2me | Theorems.Thm_TenChallenges_challenge_04_r22_disproof
-- name    : TenChallenges.challenge_04_r22_disproof
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T21:50:59.425252+00:00
-- url     : https://prove2.me/theorems/c2ba9dc9-d101-411b-8975-bf6df04862f3
-- title:
--   Challenge 4: disproof of the exact $r = 22$ Sidorenko benchmark statement
-- statement:
--   For a nonnegative integer $r$, the parameterized Sidorenko benchmark statement of Ten Challenges 04 asserts that every finite bipartite simple graph $H$ admitting a bipartition $V(H)=X\cup Y$ with $|X|\le r$ and $|Y|\le r$ satisfies Sidorenko's homomorphism-density inequality in every nonempty finite simple host graph $G$:
--
--   $$t(H,G) \ge t(K_2,G)^{|E(H)|}, \qquad t(F,G) = \frac{|\operatorname{Hom}(F,G)|}{|V(G)|^{|V(F)|}}.$$
--
--   At parameter $r=22$, this statement is false: there exist a finite simple graph $H$ admitting a bipartition $V(H)=X\cup Y$ with $|X|\le 22$ and $|Y|\le 22$, together with a nonempty finite simple graph $G$, such that
--
--   $$t(H,G) < t(K_2,G)^{|E(H)|}.$$
--
--   Specifically, the $(13,22)$ point-triple incidence graph $H$ ($13\le 22$, $22\le 22$, $|E(H)|=66$) violates Sidorenko's inequality in a finite host graph $G$. Settling this negation refutes the exact parameterized milestone `TenChallenges.statement_04 22` and implies that the parameterized Sidorenko benchmark can hold unconditionally only for $r\le 21$.
--
--   **Formalization Note.** The theorem states `¬ TenChallenges.statement_04 22` directly over `Definitions.Def_TenChallenges_Challenge_04`, where `BipartiteBoundedBy H 22` requires `H.IsBipartiteWith X Y`, `X ∪ Y = Set.univ`, `X.ncard ≤ 22`, and `Y.ncard ≤ 22`, and `SidorenkoFor H G` states `homDensity H G ≥ homDensity (completeGraph (Fin 2)) G ^ Nat.card H.edgeSet`.
-- source:
--   OpenAI, A counterexample to Sidorenko's conjecture (bipartite pattern with shore sizes 13 and 22 and 66 edges), https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/161.md ; formal finite-host theorem OAI.SidorenkoCounterexample.main (Prove2Me theorem 0ce79ce5-9403-45c0-9a5a-6c2607be713f); parameterized target TenChallenges.statement_04 22 from Ten Challenges in Combinatorics, Challenge 4, https://tenchallenges.github.io/ten-challenges/.

import Definitions.Def_TenChallenges_Challenge_04

namespace TenChallenges
theorem challenge_04_r22_disproof : ¬ TenChallenges.statement_04 22 := by sorry
end TenChallenges
