-- Prove2me | Theorems.Thm_SKHessianAscent_lemma_3_4
-- name    : SKHessianAscent.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:03:51.694803+00:00
-- url     : https://prove2.me/theorems/323f8740-87b4-4b9a-9dff-77b9429108c6
-- title:
--   Lemma 3.4 — local Hadamard theorem: $Df\succeq cI_n$ on $\Omega\supseteq B(m_0,r)$ implies $B(f(m_0),cr)\subseteq f(\Omega)$
-- statement:
--   Let $\Omega\subseteq\mathbb R^n$ be open and $f:\Omega\to\mathbb R^n$ continuously differentiable. Suppose $B(m_0,r)\subseteq\Omega$ and $Df\succeq cI_n$ on $\Omega$ for some $c>0$. Then
--
--   $$
--   B\big(f(m_0),cr\big)\subseteq f(\Omega).
--   $$
--
--   Moreover, $f$ is injective on any convex subset of $\Omega$.
--
--   The paper applies it to the map $m\mapsto\widehat y(m)$ solving the TAP equation, in dual coordinates, to convert closeness in the tilt $y$ into closeness in the magnetization $m$.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`. The Jacobian $Df(x)$ need not be symmetric; $Df\succeq cI_n$ is read as $\langle Df(x)v,v\rangle\ge c\|v\|^2$ for all $x\in\Omega$ and $v$, which for a symmetric Jacobian is the Löwner order. Balls are open. $f$ is a function on the whole space, assumed $C^1$ on $\Omega$.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, Lemma 3.4, p. 12 (cited from Ortega–Rheinboldt, Iterative Solution of Nonlinear Equations in Several Variables, 5.3.11)

import Mathlib

open scoped Topology

namespace SKHessianAscent

theorem lemma_3_4 {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hf : ContDiffOn ℝ 1 f Ω)
    (c r : ℝ) (hc : 0 < c) (m₀ : EuclideanSpace ℝ (Fin n)) (hball : Metric.ball m₀ r ⊆ Ω)
    (hD : ∀ x ∈ Ω, ∀ v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ f x v) v) :
    Metric.ball (f m₀) (c * r) ⊆ f '' Ω ∧
      ∀ K : Set (EuclideanSpace ℝ (Fin n)), K ⊆ Ω → Convex ℝ K → Set.InjOn f K := by sorry

end SKHessianAscent
