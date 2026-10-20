-- Prove2me | Theorems.Thm_SolarNonOwn_BizChoice_crossing_high_alpha
-- name    : SolarNonOwn.BizChoice.crossing_high_alpha
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:28.46566+00:00
-- url     : https://prove2.me/theorems/ce8834d5-1182-4dba-8219-10a4eda89af9
-- title:
--   Comparing A and B, Case 3, p. OA8 — single crossing at or above A₂
-- statement:
--   Suppose $A_2\le\alpha<A$. On the panel-cost interval $[0,C_0]$, the difference between the optimal $p\le r$ profit and Case B1's profit is strictly decreasing, starts positive, and is negative at $C_{A1}<C_0$:
--
--   $$D(c)=\Pi_A^*(c)-\Pi_{B1}(c),\qquad D(0)>0,\qquad D(C_{A1})<0.$$
--
--   This comparison separates the PPA-and-sales region from the sales-only region at high investment subsidy.
--
--   **Formalization Note** Strict decrease strengthens the paper's weak use of “decreasing” and rules out an interval of tied regional optima.
-- source:
--   Agrawal, Toktay & Yücel, Non-Ownership Business Models for Solar Energy, authors' manuscript of 18 Sep 2021 (MSOM, doi:10.1287/msom.2021.1049), p. OA8 (PDF p. 40), proof of Proposition 1, Comparing A and B, Case 3

import Mathlib
import Definitions.Def_SolarNonOwn_BizChoice_ClosedForms

namespace SolarNonOwn.BizChoice

/-- Comparing A and B, Case 3, p. OA8: the value gap crosses once
when A2 ≤ α. Strict decrease strengthens the paper's weak use of 'decreasing'. -/
theorem crossing_high_alpha (prm : Params) (hs : Standing prm)
    (ha : A2 prm ≤ prm.alpha) :
    (∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) (C0 prm) →
      b ∈ Set.Icc (0 : ℝ) (C0 prm) → a < b →
      profAstar prm b - profB1 prm b < profAstar prm a - profB1 prm a) ∧
    0 < profAstar prm 0 - profB1 prm 0 ∧
    profAstar prm (CA1 prm) - profB1 prm (CA1 prm) < 0 ∧
    CA1 prm < C0 prm := by sorry

end SolarNonOwn.BizChoice
