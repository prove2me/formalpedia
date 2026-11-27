-- Prove2me | Theorems.Thm_WaitTimePricing_Existence_Supplement_lemma_4
-- name    : WaitTimePricing.Existence.Supplement.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T03:40:38.563903+00:00
-- url     : https://prove2.me/theorems/fe6685af-bf9d-4d66-bf28-e813b65ecbb4
-- title:
--   Lemma 4 — positive service at an empty queue (corrected: concrete objectives)
-- statement:
--   For either revenue or social welfare, let $V=V^{\bar g}$ be the published constructed relative value function and let $F$ be the greatest-maximizer feedback (25)–(26). Under Assumption 1,
--   $$t(F(0),0)>0.$$
--   Thus the next arrival to an empty system receives strictly positive service. The claimed general-reward extension is subject to the explicit counterexample included with Theorem 2.
--
--   Differences from the source:
--   - encoding: Assumption 1 and positive arrival and service primitives → the immutable base Standing predicate, including global C³/C² extensions and λ,C>0; reason: reuse of the published model; inequalities remain on their original physical domains
--   - correction: the extension of Section 4 to every reward satisfying (V1),(V2) → positive empty-queue service for both concrete objectives; the general extension is refuted by Theorem 2’s counterexample; reason: (V1),(V2) alone permit a reward for which a continuous antitone DDE solution cannot have an empty-state maximizer
-- source:
--   Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 18, Lemma 4; p. 11, abstract reward scope

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Algorithm1
import Definitions.Def_WaitTimePricing_Existence_Supplement_Rewards

set_option autoImplicit false

namespace WaitTimePricing.Existence.Supplement
open Set

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times,
SSRN 3709573 (version of October 12, 2020), p. 18, Lemma 4.
Formalization Note: for each concrete objective the constructed base Vbar is used, with the
greatest-price maximizer and the admission-on-equality convention of (25),(26). Standing is the
immutable base predicate (global C³/C² extensions and positive λ,C). The abstract reward extension
on p. 11 is refuted in theorem_2; it is not silently covered by Objective's two constructors. -/
theorem lemma_4 (M : Model) (obj : Objective) (hM : M.Standing) :
    0 < tJoin M (feedback M (concreteReward M obj) (Vbar M obj) 0) 0 := by sorry

end WaitTimePricing.Existence.Supplement
