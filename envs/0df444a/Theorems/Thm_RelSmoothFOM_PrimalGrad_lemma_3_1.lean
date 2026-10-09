-- Prove2me | Theorems.Thm_RelSmoothFOM_PrimalGrad_lemma_3_1
-- name    : RelSmoothFOM.PrimalGrad.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:34:59.964721+00:00
-- url     : https://prove2.me/theorems/cfd48b76-80cd-4578-85e7-2a6b5a16417a
-- title:
--   Lemma 3.1, p. 345 — three-point property: φ(x) + D_h(x,z) ≥ φ(z⁺) + D_h(z⁺,z) + D_h(x,z⁺)
-- statement:
--   This is the three-point property of Tseng.
--
--   Let $Q$ be a convex subset of a finite-dimensional real inner-product space $E$, let $h:E\to\mathbb R$ be differentiable at every point of $Q$ and convex on $Q$, and let $D_h(y,x)=h(y)-h(x)-\langle\nabla h(x),y-x\rangle$ be its Bregman distance. Let $\varphi$ be convex on $Q$, let $z\in Q$, and let $z^+\in Q$ be a minimiser over $Q$ of $x\mapsto\varphi(x)+D_h(x,z)$. Then
--
--   $$\varphi(x)+D_h(x,z)\;\ge\;\varphi(z^+)+D_h(z^+,z)+D_h(x,z^+)\qquad\text{for all }x\in Q.$$
--
--   The lemma quantifies how much the proximal objective grows when one moves from the minimiser $z^+$ to any other feasible point, in terms of the Bregman distance from $z^+$. It is the step that turns one iteration of a Bregman proximal method into a telescoping inequality.
--
--   **Formalization Note** The minimiser $z^+$ is a hypothesis on a given point (it minimises over $Q$), not a value of an argmin operator, so no existence or uniqueness of minimisers is assumed or claimed. The function $\varphi$ need not be differentiable. $z\in Q$ is assumed because the paper's Bregman distance (7) is defined on $Q\times Q$.
-- source:
--   Lu, Freund & Nesterov, Relatively smooth convex optimization by first-order methods, and applications, SIAM J. Optim. 28 (2018), p. 345, Lemma 3.1

import Mathlib
import Definitions.Def_RelSmoothFOM_PrimalGrad_Setting

namespace RelSmoothFOM.PrimalGrad

theorem lemma_3_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (Q : Set E) (hQ : Convex ℝ Q) (φ : E → ℝ) (hφ : ConvexOn ℝ Q φ) (h : E → ℝ)
    (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x) (hhc : ConvexOn ℝ Q h)
    (z zp : E) (hz : z ∈ Q) (hzp : zp ∈ Q)
    (hmin : ∀ u ∈ Q, φ zp + bregman h zp z ≤ φ u + bregman h u z) :
    ∀ u ∈ Q, φ u + bregman h u z ≥ φ zp + bregman h zp z + bregman h u zp := by sorry

end RelSmoothFOM.PrimalGrad
