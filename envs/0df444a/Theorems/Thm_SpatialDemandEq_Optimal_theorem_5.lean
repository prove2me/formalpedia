-- Prove2me | Theorems.Thm_SpatialDemandEq_Optimal_theorem_5
-- name    : SpatialDemandEq.Optimal.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:07.31569+00:00
-- url     : https://prove2.me/theorems/f446780f-a89d-4c22-bad4-15c93791dc62
-- title:
--   Theorem 5, pp. 17–18 — a local optimum of (15) is a weighted Voronoi diagram with weights (16), and its rates are (17)
-- statement:
--   Under the standing assumptions of the spatial model (closed convex region $\mathcal S \subseteq \mathbb R^n$; demand $\nu$ a probability measure on $\mathcal S$ absolutely continuous w.r.t. Lebesgue measure; a continuous metric $d$ and facilities $x_1,\dots,x_K \in \mathcal S$, $K \ge 1$, with $d_k(x) = d(x,x_k)$ $\nu$-integrable and regular; $c, \lambda > 0$), let $\lambda < B$ and let $(\mu^{**}, \mathcal A^{**})$ be a local optimum of the social cost (15)
--   $$\sum_k A_k \frac{c}{\mu_k - \lambda A_k} + \sum_k \int_{\mathcal A_k} d_k\,d\nu \quad\text{subject to (10)–(12) and } \sum_k \mu_k = B,$$
--   whose areas $A^{**}_k = \nu(\mathcal A^{**}_k)$ are all positive. Put
--   $$w^{**}_k = \frac{c}{B - \lambda}\Big(\sum_j \sqrt{A^{**}_j}\Big)\frac{1}{\sqrt{A^{**}_k}}. \tag{16}$$
--   Then every $\mathcal A^{**}_k$ coincides, up to a $\nu$-null set, with the additively weighted Voronoi cell $\{x \in \mathcal S : d_k(x) + w^{**}_k \le d_j(x) + w^{**}_j \ \forall j \ne k\}$, and the service rates are
--   $$\mu^{**}_k = \lambda A^{**}_k + (B - \lambda)\frac{\sqrt{A^{**}_k}}{\sum_j \sqrt{A^{**}_j}}. \tag{17}$$
--
--   This characterizes the jointly optimized partition and service rates in closed form; Theorem 6 compares it with the decentralized equilibrium.
--
--   **Formalization Note** "Described by an additively weighted Voronoi diagram" is read as equality of each cell with the Voronoi cell up to $\nu$-null sets. The hypothesis that all areas are positive is added: at a zero area, (17) gives $\mu^{**}_k = 0$ and (16) is undefined (in Lean $1/\sqrt 0 = 0$ would give a junk weight). A local optimum uses the neighbourhood $|\mu'_k - \mu^{**}_k| < \varepsilon$, $\nu(\mathcal A'_k \triangle \mathcal A^{**}_k) < \varepsilon$; feasibility includes $\lambda A_k < \mu_k$, where (15) is finite. Integrability of each $d_k$ is added; the positive intensity $\lambda(x) > 0$ is dropped.
-- source:
--   Carlsson, Peng & Ryzhov, Demand Equilibria in Spatial Service Systems, SSRN preprint 4794156 (version of 2024-04-14), pp. 17–18, Theorem 5 (equations (15)–(17))

import Mathlib
import Definitions.Def_SpatialDemandEq_Optimal_Model

open MeasureTheory

namespace SpatialDemandEq.Optimal

theorem theorem_5 {n K : ℕ} (S : Set (E n)) (ν : Measure (E n)) (dst : E n → E n → ℝ)
    (xs : Fin K → E n) (c lam B : ℝ) (hS : Standing S ν dst xs c lam) (hB : lam < B)
    (μ : Fin K → ℝ) (A : Fin K → Set (E n))
    (hopt : IsLocalOpt ν S (distFn dst xs) c lam B μ A)
    (hpos : ∀ k, 0 < area ν (A k)) :
    (∀ k, A k =ᵐ[ν] cell S (distFn dst xs) (optWeights c lam B (areas ν A)) k) ∧
      μ = optRates lam B (areas ν A) := by sorry

end SpatialDemandEq.Optimal
