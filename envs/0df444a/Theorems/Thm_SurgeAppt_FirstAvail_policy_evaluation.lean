-- Prove2me | Theorems.Thm_SurgeAppt_FirstAvail_policy_evaluation
-- name    : SurgeAppt.FirstAvail.policy_evaluation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:33.224546+00:00
-- url     : https://prove2.me/theorems/3f5e1775-dde8-4752-b0f9-dbf5a5c416b4
-- title:
--   §6.2, p. 21 — the value of a stationary admissible policy solves the policy-evaluation equation
-- statement:
--   In the appointment-scheduling model of §3 under its standing assumptions, let $\sigma$ be a stationary admissible decision rule: at a valid book $\mathbf S$ with $a\le M$ requests it takes the action $\sigma(\mathbf S, a)$, which lies in (1). Let $V_\sigma$ be its value (9), the expected total discounted cost $\sum_{t\ge0}\beta^t\,\mathbb E[g_t]$. Then for every valid book $\mathbf S$
--
--   $$
--   V_\sigma(\mathbf S) = \sum_{a=0}^{M}\mathbb P(A=a)\Big(g\big(\mathbf S,\sigma(\mathbf S,a)\big) + \beta\sum_{\mathbf S'}\mathbb P\big(\mathbf S'\mid \mathbf S + \sigma(\mathbf S,a)\big)\,V_\sigma(\mathbf S')\Big),
--   $$
--
--   the sum over $\mathbf S'$ running over the valid books.
--
--   This is the equation the paper solves to evaluate FA, FBFS, FBLS and the LP-optimal policy in its numerical study.
-- source:
--   Grant, Gurvich, Mutharasan & Van Mieghem, Optimal dynamic appointment scheduling of base and surge capacity, SSRN 3092667 (revised July 1, 2020), p. 21, §6.2 (policy-evaluation equation)

import Mathlib
import Definitions.Def_SurgeAppt_FirstAvail_Model

namespace SurgeAppt.FirstAvail

/-- §6.2, p. 21: the value (9) of a stationary admissible policy `σ` solves the policy-evaluation
equation `V_σ(S) = ∑_a P(A = a) (g(S, σ(S, a)) + β ∑_{S'} P(S' | S + σ(S, a)) V_σ(S'))` at every
valid state. -/
theorem policy_evaluation (P : Params) (hP : P.Standing) (σ : Book P → ℕ → Book P)
    (hσ : IsAdmissible P (fun _ => σ)) (s : Book P) (hs : Valid P s) :
    value P (fun _ => σ) s =
      ∑ a ∈ Finset.range (P.M + 1), P.pA a * qValue P (value P (fun _ => σ)) s a (σ s a) := by sorry

end SurgeAppt.FirstAvail
