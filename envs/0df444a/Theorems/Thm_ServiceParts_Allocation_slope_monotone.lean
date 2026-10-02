-- Prove2me | Theorems.Thm_ServiceParts_Allocation_slope_monotone
-- name    : ServiceParts.Allocation.slope_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T22:58:28.268955+00:00
-- url     : https://prove2.me/theorems/1ac250fd-27ee-4c3e-a967-4e9ce1207c67
-- title:
--   Section 7.4 — the slopes (7.19) are nondecreasing by convexity
-- statement:
--   Let the allocation data satisfy the standing assumptions of Section 7.4 (see `AllocData`): integer gridpoints $0 = r^m_0 < r^m_1 < \cdots < r^m_{n(m)}$ with $n(m) \ge 1$, and values $c^m_n = \varphi_m(r^m_n)$ of a function $\varphi_m$ convex on $[0, \infty)$. Then the slopes $\hat c^m_n$ of (7.19) are nondecreasing in $n$: for every location $m \in M$ and every $0 < n \le n(m)$,
--   $$\hat c^m_n \ge \hat c^m_{n-1}.$$
--
--   This is the property of the data that makes the piecewise linear functions $\tilde C_m$ convex and marginal allocation exact. At $n = n(m)$ the two slopes coincide, by the definition (7.19).
--
--   **Formalization Note** Stated with $k = n - 1$: for $k < n(m)$, $\hat c^m_k \le \hat c^m_{k+1}$.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 178, Section 7.4 (sentence following Eq. (7.19))

import Mathlib
import Definitions.Def_ServiceParts_Allocation_AllocData

namespace ServiceParts.Allocation

/-- Muckstadt (2005), Section 7.4, p. 178, below (7.19): "By convexity of the original
function, we have ĉ^m_n ≥ ĉ^m_{n-1} for all n > 0" (here `n = k + 1 ≤ n(m)`). -/
theorem slope_monotone {Mbar : ℕ} (d : AllocData Mbar) (hd : d.WellFormed)
    (m : Fin Mbar) (k : ℕ) (hk : k < d.n m) :
    d.slope m k ≤ d.slope m (k + 1) := by sorry

end ServiceParts.Allocation
