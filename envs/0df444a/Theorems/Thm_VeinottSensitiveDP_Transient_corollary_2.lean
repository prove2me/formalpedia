-- Prove2me | Theorems.Thm_VeinottSensitiveDP_Transient_corollary_2
-- name    : VeinottSensitiveDP.Transient.corollary_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:52:51.673531+00:00
-- url     : https://prove2.me/theorems/f4142ebf-f1a6-4c10-8f82-41d767852105
-- title:
--   Corollary 2 — if every stationary policy is transient, V* is the unique fixed point of ℜ
-- statement:
--   In the dynamic program of §2 of Veinott (1969), suppose every stationary policy is transient. Let $V^*=\max_{f\in F}V(f^\infty)$ and $\Re V=\max_{g\in F}[r(g)+P(g)V]$ (both coordinatewise). Then
--
--   $$\Re V^*=V^*,$$
--
--   and every $V\in\mathbb R^S$ with $\Re V=V$ equals $V^*$.
--
--   This is the optimality (Bellman) equation for the expected total reward without any row-sum bound on the transition weights. Veinott's proof of Hoffman's Lemma 3 applies it with the reward $r\equiv 1$.
-- source:
--   Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria, Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1638, Corollary 2

import Mathlib
import Definitions.Def_VeinottSensitiveDP_Transient_Model
import Definitions.Def_VeinottSensitiveDP_Transient_Optimality

namespace VeinottSensitiveDP.Transient

open Matrix

variable {St : Type} [Fintype St] [DecidableEq St] [Nonempty St] {A : St → Type}
  [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)] [∀ s, Nonempty (A s)]

/-- **Corollary 2** (Veinott, *Discrete Dynamic Programming with Sensitive Discount Optimality Criteria*,
Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1638).
If every stationary policy is transient, `V*` is the unique fixed point of `ℜ`.

Here `V* ≡ max_{f ∈ F} V(f^∞)` and `ℜV ≡ max_{g ∈ F} [r(g) + P(g)V]` (p. 1637, (4)), both
coordinatewise maxima over `F`. -/
theorem corollary_2 (D : Program St A)
    (hT : ∀ g : DecisionRule St A, D.IsTransient (stationary g)) :
    D.optReturn D.vStar = D.vStar ∧ ∀ W : St → ℝ, D.optReturn W = W → W = D.vStar := by sorry

end VeinottSensitiveDP.Transient
