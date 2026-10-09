-- Prove2me | Theorems.Thm_PDScenRed_Mean_lossL_convex
-- name    : PDScenRed.Mean.lossL_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:03:01.064469+00:00
-- url     : https://prove2.me/theorems/42a5b821-1b7e-44e7-9b9a-066975beb5d5
-- title:
--   §4.3, proof of Theorem 3, p. 25, first paragraph — ζ ↦ L(ξ, ζ) is convex
-- statement:
--   Let $\mathcal Z = \{z\in\mathbb R^d_+ : Pz\le q\}$ be a nonempty bounded polytope, let $z^*:\mathbb R^d\to\mathbb R^d$ be any map, and fix $\xi\in\mathbb R^d$. Then the function
--
--   $$\zeta \longmapsto L(\xi,\zeta) = \max\Big\{\max_{z\in\mathcal Z} z'(\xi - 2\zeta),\, 0\Big\} + 2\max\{ z^*(\xi)'\zeta,\, 0\}$$
--
--   is convex on $\mathbb R^d$.
--
--   Convexity in the reduced scenario $\zeta$ is what makes the upper-bound problem (16) a convex programme, and it is the reason a zero subgradient certifies optimality in the proof of Theorem 3.
--
--   **Formalization Note** No property of $z^*$ is needed: for fixed $\xi$, $z^*(\xi)$ is a constant vector. The paper's $\mathcal Z$ is nonempty and compact (§1); the polytope is closed, so boundedness is the stated hypothesis.
-- source:
--   Bertsimas & Mundru, Optimization-based Scenario Reduction for Data-Driven Two-stage Stochastic Optimization, author manuscript (MIT DSpace), p. 25, §4.3, proof of Theorem 3, first paragraph, last sentence

import Mathlib
import Definitions.Def_PDScenRed_Mean_Setting
open scoped InnerProductSpace
open MeasureTheory

namespace PDScenRed.Mean

theorem lossL_convex {d r : ℕ} (P : Matrix (Fin r) (Fin d) ℝ) (qv : Fin r → ℝ)
    (hne : (polytope P qv).Nonempty) (hbdd : Bornology.IsBounded (polytope P qv))
    (zsel : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ξ : EuclideanSpace ℝ (Fin d)) :
    ConvexOn ℝ Set.univ (fun ζ => lossL (polytope P qv) zsel ξ ζ) := by sorry

end PDScenRed.Mean
