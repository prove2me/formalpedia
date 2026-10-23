-- Prove2me | Theorems.Thm_ShockCBM_ControlLimit_theorem_1
-- name    : ShockCBM.ControlLimit.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:32.034163+00:00
-- url     : https://prove2.me/theorems/01ca7ee7-ead4-4d76-a12b-31231f99f59d
-- title:
--   Theorem 1, p. 15 — the optimal replacement policy is a control-limit policy with limit δ^(n,t) ≤ ξ nondecreasing in age t
-- statement:
--   Consider the collapsed MDP of the shock degradation model under its standing assumptions ($\alpha_0,\beta_0,a_0,b_0>0$, $0<c_p<c_u$, $0<\gamma<1$, $\xi\ge1$, $h\ge0$, and the conjugate kernel normalisable at $(a_0+x,b_0+n)$ for every $x,n\in\mathbb N$), with value function $V$. Say that preventive replacement is optimal at a non-failed state $s=(x,n,t)$, $x<\xi$, when (19) holds:
--   $$c_p+\gamma\,\mathbb E[V(s_0+A(s_0))]\le\gamma\,\mathbb E_s[V(s+A(s))].$$
--   Then there are control limits $\delta^{(n,t)}\in\mathbb N$, one for each shock count $n$ and age $t$, such that
--   1. $\delta^{(n,t)}\le\xi$ for all $n,t$;
--   2. for all $n,t$ and every $x<\xi$, preventive replacement is optimal at $(x,n,t)$ if and only if $x\ge\delta^{(n,t)}$;
--   3. for every $n$, $t\mapsto\delta^{(n,t)}$ is non-decreasing.
--
--   The optimal policy therefore replaces a component exactly when its degradation reaches a threshold that depends on the shock count and age, and older components that have not failed are allowed to degrade further before replacement.
--
--   **Formalization Note** At $x\ge\xi$ replacement is corrective and forced, so the equivalence is posed for $x<\xi$; $\delta^{(n,t)}=\xi$ means that preventive replacement is never optimal at $(n,t)$. Since the equivalence holds for every $x<\xi$ and $\delta\le\xi$, it determines $\delta^{(n,t)}$ uniquely. Ties in (19) count as "replace".
-- source:
--   Drent, Drent, Arts, Kapodistria, Real-Time Integrated Learning and Decision Making for Cumulative Shock Degradation, Manufacturing & Service Operations Management 25(1) (2023), doi:10.1287/msom.2022.1149, accepted manuscript, p. 15, Theorem 1 (proof p. 33, (19))

import Mathlib
import Definitions.Def_ShockCBM_ControlLimit_NEF
import Definitions.Def_ShockCBM_ControlLimit_Setting

namespace ShockCBM.ControlLimit

theorem theorem_1 (M : Model) (hM : M.Standing) :
    ∃ δ : ℕ → ℕ → ℕ,
      (∀ n t : ℕ, δ n t ≤ M.ξ) ∧
      (∀ n t x : ℕ, x < M.ξ → (M.ReplaceOptimal (x, n, t) ↔ δ n t ≤ x)) ∧
      (∀ n : ℕ, Monotone (fun t => δ n t)) := by sorry

end ShockCBM.ControlLimit
