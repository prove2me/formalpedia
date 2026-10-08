-- Prove2me | Theorems.Thm_SubstitutePricing_Unified_eq_23_24
-- name    : SubstitutePricing.Unified.eq_23_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:17:51.249443+00:00
-- url     : https://prove2.me/theorems/7dfff3a3-474a-4a11-b850-f46aba3d41ef
-- title:
--   (23)–(24) — the unified optimality equation maximizes ξᵘ plus the continuation value
-- statement:
--   For each remaining time $t\ge1$ and inventory $x$, let $\pi_{t-1}$ be the unified-pricing continuation value. At every common price $r$, the one-period objective equals $\xi^u_t(x,r)+\pi_{t-1}(x)$, where
--   $$
--   \xi^u_t(x,r)=\sum_{i\in S(x)}\lambda P^i(r)\bigl(r-[\pi_{t-1}(x)-\pi_{t-1}(x-e^i)]\bigr).
--   $$
--   The optimality equation (23)–(24) says that a nonnegative common price attains the maximum of $\xi^u_t$ and that $\pi_t(x)$ equals this maximum plus $\pi_{t-1}(x)$.
--
--   **Formalization Note.** The Lean statement includes both the identity at every price and attainment on $[0,\infty)$. This also covers a sold-out inventory, where every price is optimal and $\xi^u_t=0$.
-- source:
--   Dong, Kouvelis, Tian, Dynamic Pricing and Inventory Control of Substitute Products, Manufacturing & Service Operations Management 11(2) (2009), p. 336, App. A, proof of Proposition 1, (23)–(24)

import Mathlib
import Definitions.Def_SubstitutePricing_Unified_Model

namespace SubstitutePricing.Unified

theorem eq_23_24 (M : Model) (hM : M.Assumptions) (t : ℕ) (ht : 1 ≤ t)
    (x : Fin M.n → ℕ) :
    (∀ r : ℝ, M.objU (M.piU (t - 1)) x r =
      M.xiU (M.piU (t - 1)) x r + M.piU (t - 1) x) ∧
    (∃ r : ℝ, 0 ≤ r ∧
      IsMaxOn (M.xiU (M.piU (t - 1)) x) (Set.Ici 0) r ∧
      M.piU t x = M.xiU (M.piU (t - 1)) x r + M.piU (t - 1) x) := by sorry

end SubstitutePricing.Unified
