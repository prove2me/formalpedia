-- Prove2me | Theorems.Thm_ServiceParts_StockLevels_backorder_differences
-- name    : ServiceParts.StockLevels.backorder_differences
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T07:15:07.466985+00:00
-- url     : https://prove2.me/theorems/a1704eda-f990-4402-800f-aa53d5d78252
-- title:
--   Section 3.3, p. 55 — ΔB(s) = −(1 − Σ_{x≤s} p(x)), Δ²B(s) = p(s+1): expected backorders are decreasing and discretely convex
-- statement:
--   Let an item have compound Poisson demand with steady-state resupply probabilities $p(x) = p(x \mid \lambda\bar\tau)$, ready rate $R(s) = \sum_{x \le s} p(x)$ and expected backorders $B(s) = \sum_{x > s}(x - s)\,p(x)$. Then for every stock level $s \ge 0$
--   $$\Delta B(s) = B(s+1) - B(s) = -\Big(1 - \sum_{x \le s} p(x)\Big), \qquad \Delta^2 B(s) = p(s+1) \ge 0,$$
--   so $B$ is discretely convex. If demand is simple Poisson ($u_1 = 1$), then moreover
--   $$\Delta B(s) < 0 \quad\text{and}\quad \Delta^2 B(s) > 0,$$
--   that is, $B$ is strictly decreasing and strictly discretely convex.
--
--   Convexity of $B$ is the property that makes backorder-based stocking problems tractable, in contrast with the fill rate and the ready rate.
--
--   **Formalization Note** The book derives these identities in Section 3.3 under simple Poisson demand, and uses the difference identity for compound Poisson demand on p. 61. The two identities and weak convexity are stated for compound Poisson demand (a labelled generalization); the strict statements are stated for simple Poisson demand, as in the book (for compound demand $p(s+1)$ can vanish).
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 55, Section 3.3 (ΔB(s), Δ²B(s)); p. 61, Section 3.4.2 (use for p(x|µ))

import Mathlib
import Definitions.Def_ServiceParts_StockLevels_Basic
import Definitions.Def_ServiceParts_StockLevels_CompoundPoissonDemand

namespace ServiceParts.StockLevels

theorem backorder_differences (d : CompoundPoissonDemand) (s : ℕ) :
    fdiff d.backorders s = -(1 - d.readyRate s) ∧
    fdiff2 d.backorders s = d.pmf (s + 1) ∧
    0 ≤ fdiff2 d.backorders s ∧
    (d.u 1 = 1 → fdiff d.backorders s < 0 ∧ 0 < fdiff2 d.backorders s) := by sorry

end ServiceParts.StockLevels
