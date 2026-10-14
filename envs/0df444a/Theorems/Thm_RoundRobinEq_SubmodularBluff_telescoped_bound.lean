-- Prove2me | Theorems.Thm_RoundRobinEq_SubmodularBluff_telescoped_bound
-- name    : RoundRobinEq.SubmodularBluff.telescoped_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:19:11.383026+00:00
-- url     : https://prove2.me/theorems/41437628-e249-4f3e-8f1f-e8165cf56a1a
-- title:
--   §3.2, p. 13, proof of Theorem 3.7 — telescoped bound v_i(Y) − v_i(X) ≤ v_i(X)
-- statement:
--   In the setting of Lemma 3.5 (submodular valuations, $m=kn$, a greedy bluff order $h$, an agent $i$ deviating to an arbitrary ranking $\succ_i$, with $X$ her bundle in Round-Robin$(\boldsymbol\succ^{\mathrm b})$ listed in allocation order and $Y$ her bundle in Round-Robin$(\succ_i,\boldsymbol\succ^{\mathrm b}_{-i})$ listed in Algorithm 3 order),
--   $$v_i(X)\ \ge\ v_i(Y)-v_i(X),$$
--   that is, $v_i(X)\ge\tfrac12\,v_i(Y)$.
--
--   This is the last step of the bound in Theorem 3.7: no deviation of agent $i$ from the bluff profile more than doubles her value.
--
--   **Formalization Note.** $X$ and $Y$ in the conclusion are the Round-Robin bundles `roundRobin (bluff h) i` and `roundRobin (Function.update (bluff h) i τ) i`; the listings $x$ and $y$ and their properties are hypotheses, as in Lemma 3.5.
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, p. 13, proof of Theorem 3.7, the telescoped display and the sentence after it

import Mathlib
import Definitions.Def_RoundRobinEq_SubmodularBluff_Setting
import Definitions.Def_RoundRobinEq_SubmodularBluff_Bluff
import Definitions.Def_RoundRobinEq_SubmodularBluff_Alg3

namespace RoundRobinEq.SubmodularBluff

theorem telescoped_bound {n : ℕ} [NeZero n] {M : Type*} [Fintype M] [DecidableEq M] (k : ℕ)
    (hm : Fintype.card M = k * n) (v : Fin n → Finset M → ℝ)
    (hv : ∀ i, RoundRobinEq.CancelableBluff.IsValuation (v i) ∧ IsSubmodular (v i))
    (h : List M) (hh : IsGreedyOrder v h) (i : Fin n) (τ : List M) (hτ : RoundRobinEq.CancelableBluff.IsRanking τ)
    (x : Fin k → M) (hx : ∀ j : Fin k, h[j.val * n + i.val]? = some (x j))
    (y : Fin k → M) (hy_inj : Function.Injective y)
    (hy : Finset.univ.image y = RoundRobinEq.CancelableBluff.roundRobin (Function.update (bluff h) i τ) i)
    (hy3 : IsAlg3Order (v i) x y) :
    v i (RoundRobinEq.CancelableBluff.roundRobin (Function.update (bluff h) i τ) i) - v i (RoundRobinEq.CancelableBluff.roundRobin (bluff h) i) ≤
      v i (RoundRobinEq.CancelableBluff.roundRobin (bluff h) i) := by sorry

end RoundRobinEq.SubmodularBluff
