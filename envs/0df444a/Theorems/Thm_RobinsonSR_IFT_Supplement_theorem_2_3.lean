-- Prove2me | Theorems.Thm_RobinsonSR_IFT_Supplement_theorem_2_3
-- name    : RobinsonSR.IFT.Supplement.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T16:47:25.795801+00:00
-- url     : https://prove2.me/theorems/5192e8f6-2607-427b-8a9e-781254d350b5
-- title:
--   Theorem 2.3, p. 47 — ‖x(p) − Φ_p(x₀)‖ ≤ α_ε(p)‖p − p₀‖ with α_ε(p) → 0: the linearised generalized equation (2.6) approximates x(p)
-- statement:
--   Assume the hypotheses of Theorem 2.1 and Corollary 2.2 (parameter set $S$ in a real normed space $E$, a constant $\nu$ and neighbourhoods $N_0$ of $p_0$, $V_0$ of $x_0$ with $\|f(p,x)-f(q,x)\|\le\nu\|p-q\|$ for $p,q\in N_0$, $x\in V_0$). Then for each $\varepsilon>0$ there are neighbourhoods $N_\varepsilon\subseteq N_0$ of $p_0$ and $W_\varepsilon\subseteq\Omega\cap V_0$ of $x_0$, the solution function $x(\cdot)$ of Theorem 2.1 and Corollary 2.2 on them, and, for each $p\in N_\varepsilon$, the unique solution $\Phi_p(x_0)$ in $W_\varepsilon$ of the **linear** generalized equation
--   $$0\in f(p,x_0)+f'(p_0,x_0)(x-x_0)+\partial\psi_C(x), \tag{2.6}$$
--   together with a function $\alpha_\varepsilon:N_\varepsilon\to\mathbb R$ with $\lim_{p\to p_0}\alpha_\varepsilon(p)=0$, such that for every $p\in N_\varepsilon$
--   $$\|x(p)-\Phi_p(x_0)\|\le\alpha_\varepsilon(p)\,\|p-p_0\|.$$
--
--   The solution of the nonlinear generalized equation $0\in f(p,x)+\partial\psi_C(x)$ is therefore approximated to first order in $p-p_0$ by the solution of the linearised problem (2.6), which in finite dimensions is a linear complementarity or quadratic programming problem. This is the basis of the paper's parametric sensitivity analysis.
--
--   **Formalization Note** $\Phi_p(x_0)$ is characterised, as in the paper's interpretation after the theorem, as the unique solution in $W_\varepsilon$ of (2.6); it is a function $\xi$ whose existence is part of the conclusion. $\alpha_\varepsilon$ is a real function on $S$ with $\alpha_\varepsilon(p)\to0$ as $p\to p_0$ in $S$; the limit is the content of the theorem. Corollary 2.2's hypothesis is read on fixed neighbourhoods $N_0$, $V_0$, as in that item.
-- source:
--   Robinson, Strongly regular generalized equations, Math. Oper. Res. 5 (1980), p. 47, Theorem 2.3 and its interpretation (2.6)

import Mathlib
import Definitions.Def_RobinsonSR_IFT_Setting

namespace RobinsonSR.IFT.Supplement

open scoped Topology

/-- Robinson 1980, Theorem 2.3 (p. 47): under the hypotheses of Theorem 2.1 and Corollary 2.2,
the solution `x(p)` of the nonlinear generalized equation (2.7) is approximated by the unique
solution `Φ_p(x₀)` in `V_ε` of the linear generalized equation (2.6),
`0 ∈ f(p, x₀) + f′(p₀, x₀)(x − x₀) + ∂ψ_C(x)`, with `‖x(p) − Φ_p(x₀)‖ ≤ α_ε(p)‖p − p₀‖` and
`α_ε(p) → 0` as `p → p₀`. -/
theorem theorem_2_3 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C : Set X) (hC : IsClosed C) (hCc : Convex ℝ C)
    (Ω : Set X) (hΩ : IsOpen Ω) (x0 : X) (hx0 : x0 ∈ Ω)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : Set E) (p0 : S)
    (f : S → X → StrongDual ℝ X) (f' : S → X → (X →L[ℝ] StrongDual ℝ X))
    (hf' : ∀ p, ∀ x ∈ Ω, HasFDerivAt (f p) (f' p x) x)
    (hfc : ContinuousAt (fun z : S × X => f z.1 z.2) (p0, x0))
    (hf'c : ContinuousAt (fun z : S × X => f' z.1 z.2) (p0, x0))
    (hsol : -(f p0 x0) ∈ normalCone C x0)
    (lam : ℝ) (hreg : StronglyRegular C (f p0 x0) (f' p0 x0) x0 lam)
    (nu : ℝ) (N0 : Set S) (hN0 : N0 ∈ 𝓝 p0) (V0 : Set X) (hV0 : V0 ∈ 𝓝 x0)
    (hnu : ∀ p ∈ N0, ∀ q ∈ N0, ∀ x ∈ V0, ‖f p x - f q x‖ ≤ nu * ‖(p : E) - q‖) :
    ∀ eps > 0, ∃ N ∈ 𝓝 p0, N ⊆ N0 ∧ ∃ W ∈ 𝓝 x0, W ⊆ Ω ∧ W ⊆ V0 ∧
      ∃ x : S → X, ∃ xi : S → X, ∃ alpha : S → ℝ,
      (∀ p ∈ N, x p ∈ W ∧ -(f p (x p)) ∈ normalCone C (x p) ∧
          ∀ z ∈ W, -(f p z) ∈ normalCone C z → z = x p) ∧
      (∀ p ∈ N, ∀ q ∈ N, ‖x p - x q‖ ≤ (lam + eps) * ‖f p (x q) - f q (x q)‖) ∧
      (∀ p ∈ N, ∀ q ∈ N, ‖x p - x q‖ ≤ nu * (lam + eps) * ‖(p : E) - q‖) ∧
      (∀ p ∈ N, xi p ∈ W ∧ -(f p x0 + f' p0 x0 (xi p - x0)) ∈ normalCone C (xi p) ∧
          ∀ z ∈ W, -(f p x0 + f' p0 x0 (z - x0)) ∈ normalCone C z → z = xi p) ∧
      Filter.Tendsto alpha (𝓝 p0) (𝓝 0) ∧
      ∀ p ∈ N, ‖x p - xi p‖ ≤ alpha p * ‖(p : E) - p0‖ := by sorry

end RobinsonSR.IFT.Supplement
