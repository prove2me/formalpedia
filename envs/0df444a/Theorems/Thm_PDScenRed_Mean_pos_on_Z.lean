-- Prove2me | Theorems.Thm_PDScenRed_Mean_pos_on_Z
-- name    : PDScenRed.Mean.pos_on_Z
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:02:44.369615+00:00
-- url     : https://prove2.me/theorems/e5008ed9-d908-406d-b3ee-10a6b79638a7
-- title:
--   §4.3, p. 25, paragraph after the proof of Theorem 3 — z*(ξ̄)′ξ̄ > 0 implies z′ξ̄ ≥ z*(ξ̄)′ξ̄ > 0 for all z ∈ 𝒵
-- statement:
--   Let $\mathcal Z = \{z\in\mathbb R^d_+ : Pz\le q\}$ and let $z^*:\mathbb R^d\to\mathbb R^d$ be a selection of minimizers, $z^*(\xi)\in\arg\min_{z\in\mathcal Z} z'\xi$ for every $\xi$. If $v\in\mathbb R^d$ satisfies $z^*(v)'v>0$, then every feasible decision has positive cost under $v$:
--
--   $$z'v \;\ge\; z^*(v)'v \;>\; 0 \qquad \text{for all } z\in\mathcal Z.$$
--
--   The paper applies this with $v=\bar\xi$ and Assumption 5b: every decision, in particular every $z^*(\xi)$, has $z'\bar\xi>0$, so the second clipping in $L(\xi,\bar\xi)$ is inactive.
-- source:
--   Bertsimas & Mundru, Optimization-based Scenario Reduction for Data-Driven Two-stage Stochastic Optimization, author manuscript (MIT DSpace), p. 25, §4.3, paragraph after the proof of Theorem 3, second sentence

import Mathlib
import Definitions.Def_PDScenRed_Mean_Setting
open scoped InnerProductSpace
open MeasureTheory

namespace PDScenRed.Mean

theorem pos_on_Z {d r : ℕ} (P : Matrix (Fin r) (Fin d) ℝ) (qv : Fin r → ℝ)
    (zsel : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hsel : ∀ ξ, zsel ξ ∈ SmartPTO.Fisher.Wstar (polytope P qv) ξ)
    (v : EuclideanSpace ℝ (Fin d)) (hv : 0 < ⟪zsel v, v⟫_ℝ) :
    ∀ z ∈ polytope P qv, ⟪zsel v, v⟫_ℝ ≤ ⟪z, v⟫_ℝ ∧ 0 < ⟪z, v⟫_ℝ := by sorry

end PDScenRed.Mean
