-- Prove2me | Theorems.Thm_VeinottSensitiveDP_Transient_theorem_1
-- name    : VeinottSensitiveDP.Transient.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:51:22.522217+00:00
-- url     : https://prove2.me/theorems/5224e0cd-06a8-4629-8268-60df2b7ec5f0
-- title:
--   Theorem 1 — if every stationary policy is transient: v(g, π*) > 0 gives V(g^∞) > V(π*), and v(·, π*) ≦ 0 iff V(π) ≦ V(π*) for all π
-- statement:
--   In the dynamic program of §2 of Veinott (1969), suppose every stationary policy is transient, and let $\pi^*$ be any policy. Then:
--
--   1. if $v(g,\pi^*)>0$ for some $g\in F$, then $V(g^\infty)>V(\pi^*)$;
--   2. $v(g,\pi^*)\le 0$ for all $g\in F$ if and only if $V(\pi)\le V(\pi^*)$ for all policies $\pi$.
--
--   Vectors are compared coordinatewise and $x>y$ means $x\ge y$ and $x\ne y$. This is Lemma 2 with the stationary policy $f^\infty$ replaced by an arbitrary policy and the comparison class enlarged to all policies; it gives a one-step test for optimality over all policies.
--
--   **Formalization Note.** No transience is assumed for $\pi^*$ or for $\pi$: under the hypothesis every policy is transient (Corollary 4), so all total returns are genuine series.
-- source:
--   Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria, Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1640, Theorem 1

import Mathlib
import Definitions.Def_VeinottSensitiveDP_Transient_Model

namespace VeinottSensitiveDP.Transient

open Matrix

variable {St : Type} [Fintype St] [DecidableEq St] [Nonempty St] {A : St → Type}
  [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)] [∀ s, Nonempty (A s)]

/-- **Theorem 1** (Veinott, *Discrete Dynamic Programming with Sensitive Discount Optimality Criteria*,
Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1640).
Suppose every stationary policy is transient and `π*` is a policy. If `v(g, π*) > 0` for some
`g ∈ F`, then `V(g^∞) > V(π*)`. Also `v(g, π*) ≦ 0` for all `g ∈ F` if and only if
`V(π) ≦ V(π*)` for all `π`.

**Formalization Note.** `π*` and `π` range over all policies; no transience is assumed for
them, because under the hypothesis every policy is transient (Corollary 4), so `V` is the genuine
series. `x > y` means `x ≧ y` and `x ≠ y` (coordinatewise order) and is written out. -/
theorem theorem_1 (D : Program St A)
    (hT : ∀ g : DecisionRule St A, D.IsTransient (stationary g)) (πs : Policy St A) :
    (∀ g : DecisionRule St A, 0 ≤ D.v g πs ∧ D.v g πs ≠ 0 →
      D.V πs ≤ D.V (stationary g) ∧ D.V πs ≠ D.V (stationary g)) ∧
    ((∀ g : DecisionRule St A, D.v g πs ≤ 0) ↔ ∀ π : Policy St A, D.V π ≤ D.V πs) := by sorry

end VeinottSensitiveDP.Transient
