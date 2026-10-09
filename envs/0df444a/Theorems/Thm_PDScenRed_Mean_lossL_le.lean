-- Prove2me | Theorems.Thm_PDScenRed_Mean_lossL_le
-- name    : PDScenRed.Mean.lossL_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:03:59.679347+00:00
-- url     : https://prove2.me/theorems/8a77c4eb-2318-4e2f-a46f-f17fb2f9cb6d
-- title:
--   §4.3, proof of Theorem 3, p. 25, display — L(ξ, ζ) ≤ (‖ξ‖₁ + 4‖ζ‖₁) max_{z∈𝒵} ‖z‖_∞
-- statement:
--   Let $\mathcal Z = \{z\in\mathbb R^d_+ : Pz\le q\}$ be a nonempty bounded polytope and let $z^*:\mathbb R^d\to\mathbb R^d$ be a selection of minimizers, $z^*(\xi)\in\arg\min_{z\in\mathcal Z} z'\xi$ for every $\xi$. Let $B$ be a bound on the coordinates of the feasible decisions, $|z_i|\le B$ for every $z\in\mathcal Z$ and every $i$ (for instance $B=\max_{z\in\mathcal Z}\|z\|_\infty$). Then for all $\xi,\zeta\in\mathbb R^d$,
--
--   $$\begin{aligned} L(\xi,\zeta) &\le \Big|\max_{z\in\mathcal Z} z'(\xi-2\zeta)\Big| + 2|\zeta' z^*(\xi)| \\ &\le \big(\|\xi-2\zeta\|_1 + 2\|\zeta\|_1\big) B \\ &\le \big(\|\xi\|_1 + 4\|\zeta\|_1\big) B, \end{aligned}$$
--
--   where $\|v\|_1 = \sum_i |v_i|$.
--
--   This is the bound the proof uses to see that $\mathbb E[L(\xi,\zeta)]$ is finite whenever $\mathbb E[\xi]$ is finite, and that differentiation can be moved inside the expectation.
--
--   **Formalization Note** The three inequalities of the display are stated as three conjuncts. The paper's $\max_{z\in\mathcal Z}\|z\|_\infty$ is replaced by any upper bound $B$ of it, which is equivalent: the case $B=\max_{z\in\mathcal Z}\|z\|_\infty$ is included, and every larger $B$ makes the right-hand sides larger.
-- source:
--   Bertsimas & Mundru, Optimization-based Scenario Reduction for Data-Driven Two-stage Stochastic Optimization, author manuscript (MIT DSpace), p. 25, §4.3, proof of Theorem 3, second paragraph, displayed chain

import Mathlib
import Definitions.Def_PDScenRed_Mean_Setting
open scoped InnerProductSpace
open MeasureTheory

namespace PDScenRed.Mean

theorem lossL_le {d r : ℕ} (P : Matrix (Fin r) (Fin d) ℝ) (qv : Fin r → ℝ)
    (hne : (polytope P qv).Nonempty) (hbdd : Bornology.IsBounded (polytope P qv))
    (zsel : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hsel : ∀ ξ, zsel ξ ∈ SmartPTO.Fisher.Wstar (polytope P qv) ξ)
    (B : ℝ) (hB : ∀ z ∈ polytope P qv, ∀ i, |z i| ≤ B) :
    ∀ ξ ζ : EuclideanSpace ℝ (Fin d),
      lossL (polytope P qv) zsel ξ ζ ≤
          |SmartPTO.Fisher.xi (polytope P qv) (ξ - (2 : ℝ) • ζ)| + 2 * |⟪ζ, zsel ξ⟫_ℝ| ∧
        |SmartPTO.Fisher.xi (polytope P qv) (ξ - (2 : ℝ) • ζ)| + 2 * |⟪ζ, zsel ξ⟫_ℝ| ≤
          (∑ i, |(ξ - (2 : ℝ) • ζ) i| + 2 * ∑ i, |ζ i|) * B ∧
        (∑ i, |(ξ - (2 : ℝ) • ζ) i| + 2 * ∑ i, |ζ i|) * B ≤
          (∑ i, |ξ i| + 4 * ∑ i, |ζ i|) * B := by sorry

end PDScenRed.Mean
