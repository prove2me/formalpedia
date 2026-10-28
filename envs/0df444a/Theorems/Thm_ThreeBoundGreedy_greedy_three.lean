-- Prove2me | Theorems.Thm_ThreeBoundGreedy_greedy_three
-- name    : ThreeBoundGreedy.greedy_three
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:37:41.18589+00:00
-- url     : https://prove2.me/theorems/852a121d-b3da-4929-828b-7a8f5adb725f
-- title:
--   Optimal three-tier filling under prefix capacities
-- statement:
--   Let \(n_0,n_1,n_2,c_0,c_1,c_2,a_0,a_1,a_2\) be natural numbers with \(a_0\ge a_1\ge a_2\), and assume
--   \[
--   n_0\le c_0,\quad n_0+n_1\le c_1,\quad n_0+n_1+n_2\le c_2.
--   \]
--   Define \(g_0=\min(c_0,c_1,c_2)\), \(g_1=\min(c_1,c_2)-g_0\), and \(g_2=c_2-g_0-g_1\). Then
--   \[
--   n_0a_0+n_1a_1+n_2a_2\le g_0a_0+g_1a_1+g_2a_2.
--   \]
--   Thus the largest weights may be filled first after replacing the capacities by their suffix minima. This bounds the weighted contribution of the three negative-candidate tiers.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, PrefixGreedy, lines 74–93; source SHA256 522d37d6d27d7b7feb95f651b197fb6e18e92c2dc4a065f3b52b2586a514d33d.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ThreeBoundGreedy
end ThreeBoundGreedy
open ThreeBoundGreedy

theorem ThreeBoundGreedy.greedy_three (n₀ n₁ n₂ c₀ c₁ c₂ a₀ a₁ a₂ : ℕ)
    (h₀ : n₀ ≤ c₀) (h₁ : n₀+n₁ ≤ c₁) (h₂ : n₀+n₁+n₂ ≤ c₂)
    (ha₀ : a₁ ≤ a₀) (ha₁ : a₂ ≤ a₁) :
    let g₀ := min c₀ (min c₁ c₂)
    let g₁ := min c₁ c₂-g₀
    let g₂ := c₂-(g₀+g₁)
    n₀*a₀+n₁*a₁+n₂*a₂ ≤ g₀*a₀+g₁*a₁+g₂*a₂ := by sorry
