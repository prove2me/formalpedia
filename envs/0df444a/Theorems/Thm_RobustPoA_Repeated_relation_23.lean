-- Prove2me | Theorems.Thm_RobustPoA_Repeated_relation_23
-- name    : RobustPoA.Repeated.relation_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:36:45.777135+00:00
-- url     : https://prove2.me/theorems/ba5b9c79-6f1e-4640-b1f4-a9cb34dcd801
-- title:
--   Relation (23), p. 13 — one-step smoothness bound with deviation improvements
-- statement:
--   Let $G$ be a $(\lambda,\mu)$-smooth cost-minimization game with $\mu<1$. For any played outcome $s$ and comparison outcome $s'$, define $\delta_i(s;s')=C_i(s)-C_i(s'_i,s_{-i})$. Then
--
--   $$C(s)\leq\frac{\lambda}{1-\mu}C(s')+\frac{\sum_i\delta_i(s;s')}{1-\mu}.$$
--
--   This one-step inequality is the input to the time-averaged bound in relation (25).
--
--   **Formalization Note** The paper introduces $s'$ as a minimum-cost outcome when defining $\delta_i$, but the derivation applies to every comparison outcome, as does Theorem 3.3.
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), (23), §3.2, p. 13

import Mathlib
import Definitions.Def_RobustPoA_Static_Smoothness
import Definitions.Def_RobustPoA_Repeated_Regret

namespace RobustPoA.Repeated

/-- Relation (23), allowing any comparison outcome as in the proof of Theorem 3.3. -/
theorem relation_23 {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ) (lam mu : ℝ)
    (hsm : RobustPoA.Static.IsSmooth C lam mu) (hmu : mu < 1) (s s' : ∀ i, S i) :
    RobustPoA.Static.cost C s ≤ lam / (1 - mu) * RobustPoA.Static.cost C s' +
      (∑ i, delta C s' s i) / (1 - mu) := by sorry

end RobustPoA.Repeated
