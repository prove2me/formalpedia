-- Prove2me | Theorems.Thm_RobinsonSR_IFT_theorem_2_1
-- name    : RobinsonSR.IFT.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:59:59.128817+00:00
-- url     : https://prove2.me/theorems/ad381d1b-821d-4db5-883c-124accbcd01e
-- title:
--   Theorem 2.1, p. 45 — strong regularity gives locally unique solutions x(p) with ‖x(p) − x(q)‖ ≤ (λ + ε)‖f(p, x(q)) − f(q, x(q))‖
-- statement:
--   Let $X$ be a real normed linear space with dual $X'$, $C\subseteq X$ a closed convex set, $\Omega\subseteq X$ open with $x_0\in\Omega$. Let $P$ be a topological space, $p_0\in P$, and $f:P\times\Omega\to X'$. Suppose that the partial Fréchet derivative $f'(p,x)$ of $f$ in the second variable exists on $P\times\Omega$, that $f$ and $f'$ (the latter in operator norm) are continuous at $(p_0,x_0)$, and that $x_0$ solves
--   $$0\in f(p_0,x)+\partial\psi_C(x). \tag{2.2}$$
--   If (2.2) is strongly regular at $x_0$ with associated Lipschitz constant $\lambda$, then for every $\varepsilon>0$ there are neighbourhoods $N_\varepsilon$ of $p_0$ and $W_\varepsilon\subseteq\Omega$ of $x_0$, and a function $x:N_\varepsilon\to W_\varepsilon$, such that for every $p\in N_\varepsilon$, $x(p)$ is the unique solution in $W_\varepsilon$ of
--   $$0\in f(p,x)+\partial\psi_C(x), \tag{2.3}$$
--   and for all $p,q\in N_\varepsilon$
--   $$\|x(p)-x(q)\|\le(\lambda+\varepsilon)\,\|f(p,x(q))-f(q,x(q))\|. \tag{2.4}$$
--
--   This is an implicit-function theorem for generalized equations, which cover nonlinear equations ($C=X$), complementarity problems and variational inequalities. Strong regularity is a condition on $f(p_0,x_0)$ and $f'(p_0,x_0)$ alone, and the theorem transfers it to local existence, uniqueness and Lipschitz-type stability of solutions under perturbation.
--
--   **Formalization Note** $f$ is a total function $P\times X\to X'$; its values off $P\times\Omega$ carry no hypothesis, which is why $W_\varepsilon\subseteq\Omega$ is part of the conclusion. The solution function is $x:P\to X$, with $x(p)\in W_\varepsilon$ required only for $p\in N_\varepsilon$. Uniqueness is within $W_\varepsilon$ only. $N_\varepsilon$, $W_\varepsilon$ and $x$ depend on $\varepsilon$. $X$ is not assumed complete, as on the page; the result holds for normed $X$ because $X'$ is always complete. Closedness and convexity of $C$ are kept as on the page.
-- source:
--   Robinson, Strongly regular generalized equations, Math. Oper. Res. 5 (1980), p. 45, Theorem 2.1, (2.2)–(2.4)

import Mathlib
import Definitions.Def_RobinsonSR_IFT_Setting

namespace RobinsonSR.IFT

open scoped Topology

/-- Robinson 1980, Theorem 2.1 (p. 45): implicit-function theorem for strongly regular
generalized equations `0 ∈ f(p, x) + ∂ψ_C(x)`. -/
theorem theorem_2_1 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C : Set X) (hC : IsClosed C) (hCc : Convex ℝ C)
    (Ω : Set X) (hΩ : IsOpen Ω) (x0 : X) (hx0 : x0 ∈ Ω)
    {P : Type*} [TopologicalSpace P] (p0 : P)
    (f : P → X → StrongDual ℝ X) (f' : P → X → (X →L[ℝ] StrongDual ℝ X))
    (hf' : ∀ p, ∀ x ∈ Ω, HasFDerivAt (f p) (f' p x) x)
    (hfc : ContinuousAt (fun z : P × X => f z.1 z.2) (p0, x0))
    (hf'c : ContinuousAt (fun z : P × X => f' z.1 z.2) (p0, x0))
    (hsol : -(f p0 x0) ∈ normalCone C x0)
    (lam : ℝ) (hreg : StronglyRegular C (f p0 x0) (f' p0 x0) x0 lam) :
    ∀ eps > 0, ∃ N ∈ 𝓝 p0, ∃ W ∈ 𝓝 x0, W ⊆ Ω ∧ ∃ x : P → X,
      (∀ p ∈ N, x p ∈ W ∧ -(f p (x p)) ∈ normalCone C (x p) ∧
          ∀ z ∈ W, -(f p z) ∈ normalCone C z → z = x p) ∧
      ∀ p ∈ N, ∀ q ∈ N, ‖x p - x q‖ ≤ (lam + eps) * ‖f p (x q) - f q (x q)‖ := by sorry

end RobinsonSR.IFT
