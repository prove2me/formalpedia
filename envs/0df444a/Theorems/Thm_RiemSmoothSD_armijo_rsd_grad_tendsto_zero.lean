-- Prove2me | Theorems.Thm_RiemSmoothSD_armijo_rsd_grad_tendsto_zero
-- name    : RiemSmoothSD.armijo_rsd_grad_tendsto_zero
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:27:36.663579+00:00
-- url     : https://prove2.me/theorems/2cc496a2-9575-4110-a1ce-ea7cd375c343
-- title:
--   Proposition 4.2, proof (Corollary 4.3.2 of [2]) — Armijo Riemannian steepest descent drives $\|\operatorname{grad} g\|\to0$
-- statement:
--   Let $\mathcal M$ be a smooth embedded submanifold of a finite-dimensional real inner product space $E$, $R$ a retraction on $\mathcal M$ (Definition 2.1), $g:E\to\mathbb R$ continuously differentiable, $\sigma,\beta\in(0,1)$ and $\bar\alpha>0$. Let $x_0\in\mathcal M$ and, for every $k$,
--
--   $$
--   x_{k+1}=R_{x_k}\big(\beta^{m_k}\bar\alpha\,\eta_k\big),\qquad \eta_k=-\operatorname{grad}g(x_k),
--   $$
--
--   where $m_k$ is the least natural number with $g(R_{x_k}(\beta^{m}\bar\alpha\,\eta_k))\le g(x_k)-\sigma\beta^{m}\bar\alpha\|\operatorname{grad}g(x_k)\|^2$. If the level set $\{x\in\mathcal M: g(x)\le g(x_0)\}$ is compact, then
--
--   $$
--   \lim_{k\to\infty}\|\operatorname{grad}g(x_k)\|=0 .
--   $$
--
--   This is the convergence result of Absil, Mahony and Sepulchre (Corollary 4.3.2 of reference [2] of the paper) in the form the paper applies it, with $g=\tilde f(\cdot,\mu_{\bar\ell})$, in the proof of Proposition 4.2.
--
--   Differences from the source:
--
--   - generalization: M ⊂ ℝⁿ (or a matrix space with ⟨ξ,η⟩ = Tr(ξᵀη)) → M ⊆ E, E any finite-dimensional real inner product space; reason: ℝⁿ and the matrix spaces with the trace inner product are instances, so the Lean statement specializes to the source's
--   - generalization: M a complete Riemannian submanifold embedded in ℝⁿ → M a smooth embedded submanifold of fixed dimension d (C^k coordinate-slice charts for every k), completeness not assumed; reason: completeness is not used in the argument; complete submanifolds are a special case
--   - generalization: g = f̃(·, μ_ℓ̄) with Assumption 4.1, started at x_ℓ̄ → any continuously differentiable g : E → ℝ whose level set {x ∈ M | g(x) ≤ g(x₀)} at the starting point is compact; reason: f̃(·, μ_ℓ̄) is C¹ and Assumption 4.1 with x̄ = x_ℓ̄ gives exactly this level set's compactness
--   - reading: σ in (4.1) but not on the input line of Algorithm 4.1 → σ ∈ (0,1); reason: the remark on p.15 needs σ < 1, and σ ∈ (0,1) is the Armijo convention of the cited reference [2]
--   - reading: m is the smallest integer such that (4.1) holds → m the least natural number with (4.1); reason: Armijo convention of [2], t_ℓ = β^m ᾱ ≤ ᾱ; over ℤ a least element need not exist
-- source:
--   Zhang, Chen & Ma, A Riemannian Smoothing Steepest Descent Method for Non-Lipschitz Optimization on Submanifolds, arXiv:2104.04199v1, Proposition 4.2, proof, p.16, "Using Assumption 4.1 and Corollary 4.3.2 of [2], we obtain"

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_IsSubmanifold
import Definitions.Def_ZORiem_RGD_rgrad
import Definitions.Def_RiemSmoothSD_IsSmoothRetraction
import Definitions.Def_RiemSmoothSD_RSSDRun
set_option autoImplicit false
open Filter Topology

namespace RiemSmoothSD

open ProjLikeRetr.Retractor ZORiem.RGD

/-- **Convergence of Armijo Riemannian steepest descent** (Zhang, Chen & Ma, arXiv:2104.04199v1,
Proposition 4.2, proof, p.16, "Using Assumption 4.1 and Corollary 4.3.2 of [2], we obtain
lim_{ℓ→∞} ‖grad f̃(x_ℓ, μ_ℓ̄)‖ = 0"; [2] = Absil, Mahony & Sepulchre, *Optimization Algorithms
on Matrix Manifolds*, Corollary 4.3.2). Let `M` be a smooth embedded submanifold of `E`, `R` a
retraction (Definition 2.1), `g : E → ℝ` continuously differentiable, `σ, β ∈ (0,1)`, `ᾱ > 0`.
Let `x_0 ∈ M` and `x_{k+1} = R_{x_k}(β^{m_k} ᾱ η_k)` with `η_k = −grad g(x_k)` and `m_k` the
smallest natural number with `g(R_{x_k}(β^m ᾱ η_k)) ≤ g(x_k) − σ β^m ᾱ ‖grad g(x_k)‖²`. If the
level set `{x ∈ M | g(x) ≤ g(x_0)}` is compact, then `lim_{k→∞} ‖grad g(x_k)‖ = 0`.

**Formalization Note** This is the instance of [2, Corollary 4.3.2] the paper uses, with
`g = f̃(·, μ_ℓ̄)`, the steepest-descent direction and the Armijo step of (4.1). Each step is
`IsArmijoStep`. -/
theorem armijo_rsd_grad_tendsto_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {d : ℕ} {M : Set E} (hM : ∀ k : ℕ, IsSubmanifold k d M)
    {R : E → E → E} (hR : IsSmoothRetraction M R) {g : E → ℝ} (hg : ContDiff ℝ 1 g)
    {σ β αbar : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hα : 0 < αbar)
    {x : ℕ → E} (hx0 : x 0 ∈ M) (hstep : ∀ k : ℕ, IsArmijoStep M R g σ β αbar (x k) (x (k + 1)))
    (hL : IsCompact {y | y ∈ M ∧ g y ≤ g (x 0)}) :
    Tendsto (fun k => ‖rgrad M g (x k)‖) atTop (𝓝 0) := by sorry

end RiemSmoothSD
