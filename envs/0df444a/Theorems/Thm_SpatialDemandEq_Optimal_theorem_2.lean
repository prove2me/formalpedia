-- Prove2me | Theorems.Thm_SpatialDemandEq_Optimal_theorem_2
-- name    : SpatialDemandEq.Optimal.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:14.296257+00:00
-- url     : https://prove2.me/theorems/fe5533b1-9cc2-4f6d-a75a-ac9c7d02fe29
-- title:
--   Theorem 2, p. 10 — the solution w* of the equilibrium condition (3) is unique
-- statement:
--   Assume the standing assumptions of the spatial model (closed convex $\mathcal S$, demand $\nu$ a probability measure on $\mathcal S$ absolutely continuous w.r.t. Lebesgue measure, a continuous metric, facilities in $\mathcal S$ with $K \ge 1$, integrable and regular distances, $c, \lambda > 0$) and service rates $\mu$ with $\sum_k \mu_k > \lambda$. If $w$ and $w'$ both solve the equilibrium condition
--   $$w_k = \frac{c}{\mu_k - \lambda A_k(w)}, \qquad \lambda A_k(w) < \mu_k \qquad (k = 1,\dots,K), \tag{3}$$
--   where $A_k(w)$ is the $\nu$-area of the additively weighted Voronoi cell $\mathcal A_k(w)$, then $w = w'$.
--
--   Together with the equivalence of (1) and (3), uniqueness of the weights gives uniqueness of the decentralized equilibrium partition up to null sets, which Theorem 6 uses.
-- source:
--   Carlsson, Peng & Ryzhov, Demand Equilibria in Spatial Service Systems, SSRN preprint 4794156 (version of 2024-04-14), p. 10, Theorem 2

import Mathlib
import Definitions.Def_SpatialDemandEq_Optimal_Model

open MeasureTheory

namespace SpatialDemandEq.Optimal

theorem theorem_2 {n K : ℕ} (S : Set (E n)) (ν : Measure (E n)) (dst : E n → E n → ℝ)
    (xs : Fin K → E n) (c lam : ℝ) (hS : Standing S ν dst xs c lam) (μ : Fin K → ℝ)
    (hcap : lam < ∑ k, μ k) (w w' : Fin K → ℝ)
    (hw : IsEqWeight ν S (distFn dst xs) c lam μ w)
    (hw' : IsEqWeight ν S (distFn dst xs) c lam μ w') : w = w' := by sorry

end SpatialDemandEq.Optimal
