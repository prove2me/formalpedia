-- Prove2me | Theorems.Thm_PerishablePricing_Backlog_ordered_sets_lnat_convex
-- name    : PerishablePricing.Backlog.ordered_sets_lnat_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:25:23.592138+00:00
-- url     : https://prove2.me/theorems/5162cd06-b917-437e-be95-01a3b215593d
-- title:
--   p. 287 — the ordered sets 𝒱ₙ,ₖ and 𝒱⁺ₙ,ₖ are L♮-convex
-- statement:
--   For $n \ge k \ge 0$, consider the ordered sets
--
--   $$\mathcal{V}_{n,k} = \{(s_1, \dots, s_n) \in \mathbb{R}^n : s_1 \le \dots \le s_k\}, \qquad \mathcal{V}^+_{n,k} = \{(s_1, \dots, s_n) \in \mathbb{R}^n : 0 \le s_1 \le \dots \le s_k\}.$$
--
--   Both sets are L♮-convex: for all $u, v$ in the set and all $\alpha \ge 0$, the vectors $(u + \alpha e) \wedge v$ and $u \vee (v - \alpha e)$ lie in the set again.
--
--   The state spaces and the domains of the value functions of the perishable inventory model are sets of this form, so this fact is used whenever L♮-concavity is propagated through the dynamic program.
--
--   **Formalization Note** Real case only. The sets are the `V` and `Vplus` of the shared definition file, indexed from $0$.
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, §2, p. 287 (PDF p. 5), "Note that both sets are L♮-convex"

import Mathlib
import Definitions.Def_PerishablePricing_Backlog_LNatConvex

namespace PerishablePricing.Backlog

/-- p. 287: the ordered sets `𝒱_{n,k}` and `𝒱⁺_{n,k}` are L♮-convex, for every `n` and `k ≤ n`. -/
theorem ordered_sets_lnat_convex (n k : ℕ) (hk : k ≤ n) :
    LNatConvexSet (V n k) ∧ LNatConvexSet (Vplus n k) := by sorry

end PerishablePricing.Backlog
