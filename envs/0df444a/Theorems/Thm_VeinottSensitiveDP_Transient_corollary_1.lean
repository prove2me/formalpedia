-- Prove2me | Theorems.Thm_VeinottSensitiveDP_Transient_corollary_1
-- name    : VeinottSensitiveDP.Transient.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:50:47.251388+00:00
-- url     : https://prove2.me/theorems/8278e647-4505-420a-ab56-1ddcf4fd40e1
-- title:
--   Corollary 1 — if every stationary policy is transient, some stationary policy maximizes V over the stationary policies
-- statement:
--   In the dynamic program of §2 of Veinott (1969), suppose every stationary policy is transient. Then there is $f\in F$ such that
--
--   $$V(g^\infty)\le V(f^\infty)\qquad\text{for all } g\in F,$$
--
--   coordinatewise: a single stationary policy is best among stationary policies in every starting state simultaneously.
--
--   This is what allows $V^*=\max_{f}V(f^\infty)$ to be attained by one decision rule; it extends results of Shapley and Denardo.
-- source:
--   Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria, Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1637, Corollary 1

import Mathlib
import Definitions.Def_VeinottSensitiveDP_Transient_Model

namespace VeinottSensitiveDP.Transient

open Matrix

variable {St : Type} [Fintype St] [DecidableEq St] [Nonempty St] {A : St → Type}
  [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)] [∀ s, Nonempty (A s)]

/-- **Corollary 1** (Veinott, *Discrete Dynamic Programming with Sensitive Discount Optimality Criteria*,
Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1637).
If every stationary policy is transient, there is a stationary policy that maximizes `V(·)` over
the class of stationary policies.

**Formalization Note.** "Maximizes" is in the coordinatewise order: one `f` is at least as good
as every stationary `g^∞` in every state simultaneously. -/
theorem corollary_1 (D : Program St A)
    (hT : ∀ g : DecisionRule St A, D.IsTransient (stationary g)) :
    ∃ f : DecisionRule St A, ∀ g : DecisionRule St A, D.V (stationary g) ≤ D.V (stationary f) := by sorry

end VeinottSensitiveDP.Transient
