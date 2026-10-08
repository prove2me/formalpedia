-- Prove2me | Theorems.Thm_VeinottSensitiveDP_Transient_lemma_2
-- name    : VeinottSensitiveDP.Transient.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:49:55.162233+00:00
-- url     : https://prove2.me/theorems/2b08b529-fbb7-4339-b74a-53df29db3044
-- title:
--   Lemma 2 — either some v(g, f^∞) > 0, giving V(g^∞) > V(f^∞), or all v(g, f^∞) ≦ 0, iff f^∞ is best among stationary policies
-- statement:
--   In the dynamic program of §2 of Veinott (1969), suppose every stationary policy is transient and let $f\in F$. Then:
--
--   1. either $v(g,f^\infty)>0$ for some $g\in F$, or $v(g,f^\infty)\le 0$ for all $g\in F$;
--   2. for every $g$ with $v(g,f^\infty)>0$, $V(g^\infty)>V(f^\infty)$;
--   3. $v(g,f^\infty)\le 0$ for all $g\in F$ if and only if $V(g^\infty)\le V(f^\infty)$ for all $g\in F$.
--
--   Here vectors are compared coordinatewise and $x>y$ means $x\ge y$ and $x\ne y$. With this reading item 1 is not a tautology: a $g$ for which $v(g,f^\infty)$ has coordinates of both signs satisfies neither alternative, and item 1 says that in that case some other $g$ satisfies the first one.
--
--   The lemma is the policy-improvement step of Howard's method in the transient model; iterating it gives Corollary 1.
-- source:
--   Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria, Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1637, Lemma 2

import Mathlib
import Definitions.Def_VeinottSensitiveDP_Transient_Model

namespace VeinottSensitiveDP.Transient

open Matrix

variable {St : Type} [Fintype St] [DecidableEq St] [Nonempty St] {A : St → Type}
  [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)] [∀ s, Nonempty (A s)]

/-- **Lemma 2** (Veinott, *Discrete Dynamic Programming with Sensitive Discount Optimality Criteria*,
Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1637).
Suppose `f ∈ F` and every stationary policy is transient. Then either `v(g, f^∞) > 0` for some
`g ∈ F` or `v(g, f^∞) ≦ 0` for all `g ∈ F`. In the former case `V(g^∞) > V(f^∞)`. The latter
case occurs if and only if `V(g^∞) ≦ V(f^∞)` for all `g ∈ F`.

**Formalization Note.** Vectors in `St → ℝ` are ordered coordinatewise; Veinott's `x > y` means
`x ≧ y` and `x ≠ y` and is written out. "In the former case" refers to the `g` with
`v(g, f^∞) > 0`. -/
theorem lemma_2 (D : Program St A) (f : DecisionRule St A)
    (hT : ∀ g : DecisionRule St A, D.IsTransient (stationary g)) :
    ((∃ g : DecisionRule St A, 0 ≤ D.v g (stationary f) ∧ D.v g (stationary f) ≠ 0) ∨
      ∀ g : DecisionRule St A, D.v g (stationary f) ≤ 0) ∧
    (∀ g : DecisionRule St A, 0 ≤ D.v g (stationary f) ∧ D.v g (stationary f) ≠ 0 →
      D.V (stationary f) ≤ D.V (stationary g) ∧ D.V (stationary f) ≠ D.V (stationary g)) ∧
    ((∀ g : DecisionRule St A, D.v g (stationary f) ≤ 0) ↔
      ∀ g : DecisionRule St A, D.V (stationary g) ≤ D.V (stationary f)) := by sorry

end VeinottSensitiveDP.Transient
