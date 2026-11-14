-- Prove2me | Theorems.Thm_TenChallenges_challenge_04_disproof
-- name    : TenChallenges.challenge_04_disproof
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T02:42:49.937198+00:00
-- url     : https://prove2.me/theorems/0f7f24fc-7788-4971-9601-6c4cb14b94cf
-- title:
--   Sidorenko counterexample in the exact Ten Challenges definitions
-- statement:
--   There exist finite simple graphs $H$ and $G$, with $G$ nonempty and $H$ bipartite, such that
--
--   $$t(H,G)<t(K_2,G)^{|E(H)|}.$$
--
--   Here $t(F,G)$ counts all edge-preserving vertex maps, including noninjective ones, divided by $|V(G)|^{|V(F)|}$. This is the negation of the unscaled Sidorenko conjecture stated by Ten Challenges 04, using that mission's exact definitions. It transfers the existing finite counterexample to the canonical challenge interface.
-- source:
--   OpenAI, A counterexample to Sidorenko's conjecture, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/161.md ; formal finite-host theorem OAI.SidorenkoCounterexample.main (Prove2Me theorem 0ce79ce5-9403-45c0-9a5a-6c2607be713f). Canonical target: TenChallenges.challenge_04.

import Definitions.Def_TenChallenges_Challenge_04
open SimpleGraph

namespace TenChallenges
theorem challenge_04_disproof :
    ¬ (∀ {W V : Type} [Fintype W] [Fintype V] [Nonempty V]
      (H : SimpleGraph W) (G : SimpleGraph V),
      (∃ X Y : Set W, H.IsBipartiteWith X Y ∧ X ∪ Y = Set.univ) →
      SidorenkoFor H G) := by sorry
end TenChallenges
