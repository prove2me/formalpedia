-- Prove2me | Theorems.Thm_PlatformPrecommit_KS_lemma_7
-- name    : PlatformPrecommit.KS.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:05:41.127219+00:00
-- url     : https://prove2.me/theorems/acd86cdf-c0b4-478b-aa6c-236c8229a047
-- title:
--   Lemma 7, p. 15 — demand and supply equal committed capacity in equilibrium
-- statement:
--   In every subgame-perfect equilibrium of the two-stage capacity-precommitment game, each platform's second-stage demand and supply equal its first-stage capacity:
--
--   $$d_i(p)=s_i(w)=q_i\qquad (i=1,2).$$
--
--   Thus both sides of the market clear at the capacity chosen by the platform. This is the binding-capacity step used by Proposition 1.
--
--   **Formalization Note** The two-stage equilibrium selects positive profit for each platform whenever a subgame equilibrium permits that platform positive profit, even if its rival has zero capacity. This resolves the manuscript's unqualified equilibrium wording, since zero-profit continuation equilibria can otherwise punish deviations. Prices and wages are chosen jointly, and first-stage deviations re-play the continuation game.
-- source:
--   Hu, Liu, Precommitments in Two-Sided Market Competition, submitted manuscript (SSRN 3734828; TSpace), p. 15, Lemma 7; Online Appendix pp. 32–33, proof of Lemma 7

import Mathlib
import Definitions.Def_PlatformPrecommit_KS_Setting

namespace PlatformPrecommit.KS

/-- Lemma 7, p. 15: capacities bind in every selected subgame-perfect equilibrium. -/
theorem lemma_7 (M : Model) (hM : M.Standing) :
    ∀ q σ, M.IsSPE q σ → ∀ i : Fin 2,
      M.demand (σ q).1 i = q i ∧ M.supply (σ q).2 i = q i := by sorry

end PlatformPrecommit.KS
