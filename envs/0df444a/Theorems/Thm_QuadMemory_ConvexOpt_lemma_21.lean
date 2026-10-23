-- Prove2me | Theorems.Thm_QuadMemory_ConvexOpt_lemma_21
-- name    : QuadMemory.ConvexOpt.lemma_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:10.98439+00:00
-- url     : https://prove2.me/theorems/c09e5af2-958a-464a-8eb5-0043befb308d
-- title:
--   Lemma 21, p. 37 — a uniform vector of a d^{−3}-slab around k ≤ d/3−1 orthonormal vectors, and its discretization, rarely correlate with a fixed x
-- statement:
--   Let $0\le k\le d/3-1$, let $x_1,\dots,x_k\in\mathbb R^d$ be orthonormal and let $x\in B_d(0,1)$. Let $\mu$ be the uniform distribution on $S^{d-1}\cap\{w:|x_i^\top w|\le d^{-3},\ i\le k\}$ and $y\sim\mu$.
--
--   1. For every $t\ge2$,
--   $$\mathbb P\Big(|x^\top y|\ge\sqrt{\frac td}+\frac1{d^2}\Big)\le2\sqrt t\,e^{-t/3}.$$
--   2. Let $\delta\le1$ and let $\varphi$ be any map with $\|\varphi(y)-y\|\le\delta$ for every unit vector $y$, for instance the discretization $\varphi_\delta$. Then for every $t\ge4$, with $z=\varphi(y)$,
--   $$\mathbb P\Big(|x^\top z|\ge\sqrt{\frac td}+\frac1{d^2}+\delta\Big)\le2\sqrt t\,e^{-t/3}.$$
--
--   The hidden vectors of the hard instance are sampled this way, so the lemma bounds how much any query can learn about them.
--
--   **Formalization Note.** $\mu$ is the uniform sphere law conditioned on the slab. The second claim is stated for every map within distance $\delta$ of the identity on the sphere; the proof uses only this property of $\varphi_\delta$, so the statement covers the page's. The probability of the second claim is the (outer) measure of $\{y:|x^\top\varphi(y)|\ge\cdots\}$, so $\varphi$ needs no measurability.
-- source:
--   Blanchard, Zhang & Jaillet, arXiv:2302.04963v2, p. 37, Lemma 21

import Mathlib
import Definitions.Def_QuadMemory_ConvexOpt_Model
import Definitions.Def_QuadMemory_ConvexOpt_Game

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace QuadMemory.ConvexOpt

/-- Lemma 21 (p. 37): let `0 ≤ k ≤ d/3 - 1`, let `x_1, …, x_k` be orthonormal, `x` in the unit
ball, and `μ` the uniform law on `S^{d-1} ∩ {w : |x_iᵀ w| ≤ d^{-3}, i ≤ k}`. For `y ∼ μ`:
(1) for `t ≥ 2`, `P(|xᵀy| ≥ √(t/d) + 1/d²) ≤ 2√t e^{-t/3}`;
(2) for `δ ≤ 1`, any `φ` with `‖φ(y) - y‖ ≤ δ` on the sphere (such as `φ_δ`) and `t ≥ 4`,
`P(|xᵀφ(y)| ≥ √(t/d) + 1/d² + δ) ≤ 2√t e^{-t/3}`. -/
theorem lemma_21 (d k : ℕ) (hk : (k : ℝ) ≤ (d : ℝ) / 3 - 1) (xs : Fin k → E d)
    (hxs : Orthonormal ℝ xs) (x : E d) (hx : x ∈ Metric.closedBall (0 : E d) 1) :
    (∀ t : ℝ, 2 ≤ t →
      ((sphereLaw d)[|{w : E d | ‖w‖ = 1 ∧ ∀ i, |⟪xs i, w⟫| ≤ ((d : ℝ) ^ 3)⁻¹}])
          {y | Real.sqrt (t / d) + 1 / (d : ℝ) ^ 2 ≤ |⟪x, y⟫|} ≤
        ENNReal.ofReal (2 * Real.sqrt t * Real.exp (-(t / 3)))) ∧
    (∀ δ : ℝ, δ ≤ 1 → ∀ φ : E d → E d,
      (∀ y ∈ Metric.sphere (0 : E d) 1, ‖φ y - y‖ ≤ δ) → ∀ t : ℝ, 4 ≤ t →
      ((sphereLaw d)[|{w : E d | ‖w‖ = 1 ∧ ∀ i, |⟪xs i, w⟫| ≤ ((d : ℝ) ^ 3)⁻¹}])
          {y | Real.sqrt (t / d) + 1 / (d : ℝ) ^ 2 + δ ≤ |⟪x, φ y⟫|} ≤
        ENNReal.ofReal (2 * Real.sqrt t * Real.exp (-(t / 3)))) := by sorry

end QuadMemory.ConvexOpt
