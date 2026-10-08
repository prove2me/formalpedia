-- Prove2me | Theorems.Thm_RobustDP_Discounted_lemma3_dynamic_static
-- name    : RobustDP.Discounted.lemma3_dynamic_static
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:47:16.316981+00:00
-- url     : https://prove2.me/theorems/a3b18358-4d76-493f-a33a-314ace06e788
-- title:
--   Lemma 3 (Dynamic vs Static adversary) — a stationary policy has the same value in the dynamic and the static model
-- statement:
--   Let $(\mathcal S,\mathcal A,\mathcal P,r,\lambda)$ be a discounted ambiguous MDP, let $q$ be a randomized Markov decision rule ($q_s\in\mathcal M(\mathcal A(s))$ for every $s$), and let $\pi=(q,q,\dots)$ be the stationary policy. Let $V^\pi_\lambda$ be its value against the dynamic adversary and $\hat V^\pi_\lambda$ its value against the static adversary, who fixes one $\bar p_{sa}\in\mathcal P(s,a)$ per state–action pair. Then for every state $s$,
--   $$\hat V^\pi_\lambda(s)=V^\pi_\lambda(s).$$
--
--   For stationary policies the adversary's best response is static, so the optimal stationary policy of the static model is obtained from (30).
--
--   **Formalization Note** The page states the lemma for "any decision rule" and proves it for deterministic rules, adding that "the same technique extends to randomized policies". It is stated here for randomized Markov rules, which include the deterministic ones as point masses.
-- source:
--   Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07 (rev. May 4, 2004), p. 14, Lemma 3; static model, p. 9

import Mathlib
import Definitions.Def_RobustDP_Discounted_Model
import Definitions.Def_RobustDP_Discounted_Value
import Definitions.Def_RobustDP_Discounted_Bellman

namespace RobustDP.Discounted

theorem lemma3_dynamic_static {S A : Type*} [Countable S] [Countable A] (M : Model S A)
    (q : RandRule M) (s : S) :
    Vstatic M (stationaryRand M q) s = V M (stationaryRand M q) s := by sorry

end RobustDP.Discounted
