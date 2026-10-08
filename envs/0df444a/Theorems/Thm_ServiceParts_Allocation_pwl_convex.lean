-- Prove2me | Theorems.Thm_ServiceParts_Allocation_pwl_convex
-- name    : ServiceParts.Allocation.pwl_convex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T23:02:01.497982+00:00
-- url     : https://prove2.me/theorems/9f9d8c9d-02d2-4a68-9066-ba9de720f079
-- title:
--   Proof of Proposition 2 — the piecewise linear functions (7.20) are convex
-- statement:
--   Under the standing assumptions of Section 7.4 (see `AllocData`), for every location $m \in M$ the piecewise linear approximation
--   $$\tilde C_m(r) = c^m_0 + \sum_{n=0}^{n(m)-1} \mathbf 1_{\{r \ge r^m_n\}} \bigl(r \wedge r^m_{n+1} - r^m_n\bigr)\, \hat c^m_n + \mathbf 1_{\{r \ge r^m_{n(m)}\}} \bigl(r - r^m_{n(m)}\bigr)\, \hat c^m_{n(m)}$$
--   of (7.20)–(7.21) is a convex function of $r$ on $[0, \infty)$.
--
--   The proof of Proposition 2 invokes this convexity to justify that the marginal analysis algorithm AllocOpt solves the allocation problem (7.22).
--
--   **Formalization Note** Convexity is asserted on $[0, \infty)$, the domain of the allocations. For $r < 0$ every indicator vanishes and $\tilde C_m$ is constant, so $\tilde C_m$ is in general not convex on all of $\mathbb R$ (when $\hat c^m_0 < 0$).
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 179, proof of Proposition 2 (convexity of (7.20)-(7.21))

import Mathlib
import Definitions.Def_ServiceParts_Allocation_AllocData

namespace ServiceParts.Allocation

/-- Muckstadt (2005), proof of Proposition 2, p. 179: the piecewise linear functions
`Ĉ_m` of (7.20)–(7.21) are convex on `ℝ⁺`. -/
theorem pwl_convex {Mbar : ℕ} (d : AllocData Mbar) (hd : d.WellFormed) (m : Fin Mbar) :
    ConvexOn ℝ (Set.Ici 0) (d.pwl m) := by sorry

end ServiceParts.Allocation
