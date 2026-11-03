-- Prove2me | Theorems.Thm_RiemSmoothSD_line_search_well_defined
-- name    : RiemSmoothSD.line_search_well_defined
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:27:37.819224+00:00
-- url     : https://prove2.me/theorems/78b4d9ba-c4dc-4f83-a6f7-07e9bde4d6f9
-- title:
--   Algorithm 4.1, remark — the Armijo line search (4.1) is well defined
-- statement:
--   Let $\mathcal M$ be a smooth embedded submanifold of a finite-dimensional real inner product space $E$, $R$ a retraction on $\mathcal M$ (Definition 2.1), and $\mu$ such that $\tilde f(\cdot,\mu)$ is continuously differentiable on $E$. Let $\sigma,\beta\in(0,1)$, $\bar\alpha>0$, and let $x\in\mathcal M$ with $\operatorname{grad}\tilde f(x,\mu)\ne0$. Put $\eta=-\operatorname{grad}\tilde f(x,\mu)$. Then there is $m\in\mathbb N$ with
--
--   $$
--   \tilde f\big(R_x(\beta^m\bar\alpha\,\eta),\mu\big)\le\tilde f(x,\mu)-\sigma\beta^m\bar\alpha\,\|\operatorname{grad}\tilde f(x,\mu)\|^2 .
--   $$
--
--   So the step size $t_\ell=\beta^m\bar\alpha$ of Algorithm 4.1 is found after finitely many trials whenever the algorithm reaches line 11.
--
--   Differences from the source:
--
--   - generalization: M ⊂ ℝⁿ (or a matrix space with ⟨ξ,η⟩ = Tr(ξᵀη)) → M ⊆ E, E any finite-dimensional real inner product space; reason: ℝⁿ and the matrix spaces with the trace inner product are instances, so the Lean statement specializes to the source's
--   - generalization: M a complete Riemannian submanifold embedded in ℝⁿ → M a smooth embedded submanifold of fixed dimension d (C^k coordinate-slice charts for every k), completeness not assumed; reason: completeness is not used in the argument; complete submanifolds are a special case
--   - generalization: f̃ a smoothing function of f (Definition 2.7) → only f̃(·, μ) continuously differentiable for the fixed μ; reason: the remark uses only this property ("for fixed μ_ℓ, f̃(·, μ_ℓ) is continuously differentiable"); every smoothing function has it
--   - generalization: the current iterate x_ℓ reaching line 11 → any x ∈ M with grad f̃(x, μ) ≠ 0; reason: every iterate reaching line 11 has ‖η_ℓ‖ > δ_ℓ > 0, so it is such a point
--   - reading: σ in (4.1) but not on the input line of Algorithm 4.1 → σ ∈ (0,1); reason: the remark on p.15 needs σ < 1, and σ ∈ (0,1) is the Armijo convention of the cited reference [2]
--   - reading: m is the smallest integer such that (4.1) holds → m the least natural number with (4.1); reason: Armijo convention of [2], t_ℓ = β^m ᾱ ≤ ᾱ; over ℤ a least element need not exist
-- source:
--   Zhang, Chen & Ma, A Riemannian Smoothing Steepest Descent Method for Non-Lipschitz Optimization on Submanifolds, arXiv:2104.04199v1, Algorithm 4.1, remark, p.15, "the line search (4.1) is well defined and tℓ can be found in finite trials"

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_IsSubmanifold
import Definitions.Def_ZORiem_RGD_rgrad
import Definitions.Def_RiemSmoothSD_IsSmoothRetraction
import Definitions.Def_RiemSmoothSD_RSSDRun
set_option autoImplicit false

namespace RiemSmoothSD

open ProjLikeRetr.Retractor ZORiem.RGD

/-- **The line search (4.1) is well defined** (Zhang, Chen & Ma, arXiv:2104.04199v1,
Algorithm 4.1, remark, p.15, "the line search (4.1) is well defined and t_ℓ can be found in finite
trials"). Let `M` be a smooth embedded submanifold of `E`, `R` a retraction (Definition 2.1),
`μ` a smoothing parameter with `f̃(·, μ)` continuously differentiable, `σ, β ∈ (0,1)`, `ᾱ > 0`,
and `x ∈ M` with `grad f̃(x, μ) ≠ 0`. Then some `m ∈ ℕ` satisfies the Armijo condition (4.1)
`f̃(R_x(β^m ᾱ η), μ) ≤ f̃(x, μ) − σ β^m ᾱ ‖grad f̃(x, μ)‖²` with `η = −grad f̃(x, μ)`.

**Formalization Note** `E` is a finite-dimensional real inner product space, `M` a `C^k`
coordinate-slice submanifold of dimension `d` for every `k`, `R : E → E → E` with
`IsSmoothRetraction M R`; only the `C¹` property of `f̃(·, μ)` is assumed (the remark's
"for fixed μ_ℓ, f̃(·, μ_ℓ) is continuously differentiable"). When `grad f̃(x, μ) = 0`, Algorithm 4.1
never reaches the line search, because `‖η_ℓ‖ = 0 ≤ δ_ℓ`. -/
theorem line_search_well_defined {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {d : ℕ} {M : Set E} (hM : ∀ k : ℕ, IsSubmanifold k d M)
    {R : E → E → E} (hR : IsSmoothRetraction M R) {ftilde : E → ℝ → ℝ} {μ : ℝ}
    (hC1 : ContDiff ℝ 1 (fun z => ftilde z μ)) {σ β αbar : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hα : 0 < αbar) {x : E} (hx : x ∈ M)
    (hgrad : rgrad M (fun z => ftilde z μ) x ≠ 0) :
    ∃ m : ℕ, ArmijoHolds M R (fun z => ftilde z μ) σ β αbar x m := by sorry

end RiemSmoothSD
