-- Prove2me | Theorems.Thm_VeinottSensitiveDP_Transient_corollary_6
-- name    : VeinottSensitiveDP.Transient.corollary_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:51:13.348367+00:00
-- url     : https://prove2.me/theorems/421eb7f7-4350-4ea5-95f9-878b6399d32d
-- title:
--   Corollary 6 — if every stationary policy is transient, a stationary policy maximizes V over all policies
-- statement:
--   Consider a dynamic program with finitely many states $1,\dots,S$, a finite nonempty action set $A_s$ in each state, real rewards $r(s,a)$ and nonnegative transition weights $p(t\mid s,a)$ whose row sums are not required to be at most one (§2 of Veinott 1969). A policy is a sequence $\pi=(f_1,f_2,\dots)$ of decision rules, and its total return is $V(\pi)=\sum_{N\ge 0}P^N(\pi)r(f_{N+1})$. If every stationary policy is transient, then there is a decision rule $f\in F$ such that
--
--   $$V(\pi)\le V(f^\infty)\qquad\text{for every policy }\pi,$$
--
--   coordinatewise, i.e. in every starting state.
--
--   This extends Blackwell's result that $V(\cdot)$ attains its maximum over all policies among the stationary policies from the case $\|P(g)\|<1$ for all $g$ to the weaker hypothesis that each stationary policy is transient.
--
--   **Formalization Note.** Policies are all sequences of decision rules indexed from $0$ (deterministic, Markov, possibly time-dependent). No transience is assumed for the competing policy $\pi$: under the hypothesis every policy is transient (Corollary 4), so $V(\pi)$ is the genuine absolutely convergent series and not the default value of Lean's `tsum`.
-- source:
--   Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria, Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1640, Corollary 6

import Mathlib
import Definitions.Def_VeinottSensitiveDP_Transient_Model

namespace VeinottSensitiveDP.Transient

open Matrix

variable {St : Type} [Fintype St] [DecidableEq St] [Nonempty St] {A : St → Type}
  [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)] [∀ s, Nonempty (A s)]

/-- **Corollary 6** (Veinott, *Discrete Dynamic Programming with Sensitive Discount Optimality Criteria*,
Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1640).
If every stationary policy is transient, there is a stationary policy that maximizes `V(·)` over
the class of all policies.

**Formalization Note.** Policies are all sequences `ℕ → F` of decision rules (deterministic,
Markov, possibly time-dependent), and "maximizes" is in the coordinatewise order: one stationary
`f^∞` is at least as good as every policy in every state. No transience is assumed for the
competing policy `π`: under the hypothesis every policy is transient (Corollary 4), so `V π` is
the genuine, absolutely convergent series and not the default value of `tsum`. -/
theorem corollary_6 (D : Program St A)
    (hT : ∀ g : DecisionRule St A, D.IsTransient (stationary g)) :
    ∃ f : DecisionRule St A, ∀ π : Policy St A, D.V π ≤ D.V (stationary f) := by sorry

end VeinottSensitiveDP.Transient
