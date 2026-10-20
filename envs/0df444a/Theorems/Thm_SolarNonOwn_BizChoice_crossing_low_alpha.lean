-- Prove2me | Theorems.Thm_SolarNonOwn_BizChoice_crossing_low_alpha
-- name    : SolarNonOwn.BizChoice.crossing_low_alpha
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:07.46039+00:00
-- url     : https://prove2.me/theorems/c99b9d75-c539-43d0-a8a4-96182d053199
-- title:
--   Comparing A and B, Cases 1–2, pp. OA7–OA8 — single crossing below A₂
-- statement:
--   Suppose $\alpha<A_2$. On the panel-cost interval $[0,C_0]$, the difference between the optimal $p\le r$ profit and Case B2's profit is strictly decreasing, starts positive, and is negative at $C_{A2}$:
--
--   $$D(c)=\Pi_A^*(c)-\Pi_{B2}(c),\qquad D(0)>0,\qquad D(C_{A2})<0.$$
--
--   Consequently the regional profit comparison changes sign only once. This combines the paper's Cases 1 and 2, where the active A branch depends on $\alpha$.
--
--   **Formalization Note** The source calls the difference “decreasing” and uses that term weakly; strict decrease is the disclosed strengthening needed to exclude an interval of tied optima.
-- source:
--   Agrawal, Toktay & Yücel, Non-Ownership Business Models for Solar Energy, authors' manuscript of 18 Sep 2021 (MSOM, doi:10.1287/msom.2021.1049), pp. OA7–OA8 (PDF pp. 39–40), proof of Proposition 1, Comparing A and B, Cases 1–2

import Mathlib
import Definitions.Def_SolarNonOwn_BizChoice_ClosedForms

namespace SolarNonOwn.BizChoice

/-- Comparing A and B, Cases 1–2, pp. OA7–OA8: the value gap crosses once
when α < A2. Strict decrease strengthens the paper's weak use of 'decreasing'. -/
theorem crossing_low_alpha (prm : Params) (hs : Standing prm)
    (ha : prm.alpha < A2 prm) :
    (∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) (C0 prm) →
      b ∈ Set.Icc (0 : ℝ) (C0 prm) → a < b →
      profAstar prm b - profB2 prm b < profAstar prm a - profB2 prm a) ∧
    0 < profAstar prm 0 - profB2 prm 0 ∧
    profAstar prm (CA2 prm) - profB2 prm (CA2 prm) < 0 := by sorry

end SolarNonOwn.BizChoice
