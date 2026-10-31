-- Prove2me | Theorems.Thm_WainwrightHDS_NucNorm_cone_constraint_nuclear
-- name    : WainwrightHDS.NucNorm.cone_constraint_nuclear
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-30T00:34:04.633149+00:00
-- url     : https://prove2.me/theorems/c6c0530d-5261-4177-a8d5-e4c59ed367f7
-- title:
--   Eq. (10.15) — cone constraint for nuclear-norm regularized M-estimators
-- statement:
--   Let $\mathcal L:\mathbb R^{d_1\times d_2}\to\mathbb R$ and $\Theta^*\in\mathbb R^{d_1\times d_2}$, and let $G$ be a subgradient of $\mathcal L$ at $\Theta^*$ in the trace inner product:
--
--   $$
--   \mathcal L(\Theta^*) + \langle\!\langle G,\Delta\rangle\!\rangle \;\le\; \mathcal L(\Theta^*+\Delta)\qquad\text{for all }\Delta
--   $$
--
--   (for a convex differentiable $\mathcal L$, $G=\nabla\mathcal L(\Theta^*)$). Let $\lambda>0$ with $\lambda\ge 2\,|||G|||_2$, and let $\widehat\Theta$ be any global minimizer of $\Theta\mapsto\mathcal L(\Theta)+\lambda|||\Theta|||_{\mathrm{nuc}}$. Then for every pair of subspaces $\mathbb U\subseteq\mathbb R^{d_1}$, $\mathbb V\subseteq\mathbb R^{d_2}$, with $\mathbb M=\mathbb M(\mathbb U,\mathbb V)$ and $\overline{\mathbb M}=\overline{\mathbb M}(\mathbb U,\mathbb V)$, the error $\widehat\Delta=\widehat\Theta-\Theta^*$ satisfies
--
--   $$
--   |||\widehat\Delta_{\overline{\mathbb M}^\perp}|||_{\mathrm{nuc}} \;\le\; 3\,|||\widehat\Delta_{\overline{\mathbb M}}|||_{\mathrm{nuc}} + 4\,|||\Theta^*_{\mathbb M^\perp}|||_{\mathrm{nuc}} ,
--   $$
--
--   where subscripts denote orthogonal projections in the trace inner product. The constraint confines the error to a cone around the model subspace, on which restricted strong convexity is applied.
--
--   Differences from the source:
--   - generalization: L_n convex and differentiable, λ_n ≥ 2|||∇L_n(Θ*)|||₂ → any L with a subgradient G at Θ* (L(Θ*) + ⟨⟨G, Δ⟩⟩ ≤ L(Θ* + Δ) for all Δ) and 2|||G|||₂ ≤ λ; reason: for convex differentiable L_n the gradient ∇L_n(Θ*) is such a G, so it specializes to the source
--   - generalization: M = M(U^r, V^r), M̄ = M̄(U^r, V^r) for the top-r singular subspaces of Θ* → M(U, V), M̄(U, V) for arbitrary subspaces U, V; reason: the bound holds for every pair, so it specializes to the source's pair
--   - encoding: projections Δ̂_M̄, Δ̂_M̄⊥, Θ*_M⊥ (trace-inner-product projections (9.20)) → Δ − P_{U⊥}ΔP_{V⊥}, P_{U⊥}ΔP_{V⊥}, Θ* − P_UΘ*P_V; reason: these formulas are the orthogonal projections onto M̄, M̄⊥ and M⊥
-- source:
--   Wainwright, High-Dimensional Statistics: A Non-Asymptotic Viewpoint, Cambridge University Press 2019, doi:10.1017/9781108627771, §10.2.1, pp. 318–319 (PDF pp. 338–339), Eq. (10.15); λ_n > 0 from (9.3), p. 260 (PDF p. 280)

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_traceInner
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2
import Definitions.Def_WainwrightHDS_NucNorm_projMbar
import Definitions.Def_WainwrightHDS_NucNorm_projMperp

namespace WainwrightHDS.NucNorm

/-- **Eq. (10.15): cone constraint for nuclear-norm regularized M-estimators.** Let
`L : ℝ^{d₁×d₂} → ℝ`, let `G` satisfy `L(Θ*) + ⟨⟨G, Δ⟩⟩ ≤ L(Θ* + Δ)` for all `Δ` (for a convex
differentiable `L`, `G = ∇L(Θ*)`), let `λ > 0` with `λ ≥ 2 |||G|||₂`, and let `Θ̂` be a global
minimizer of `Θ ↦ L(Θ) + λ |||Θ|||_nuc`. Then for any subspaces `𝕌`, `𝕍`, the error `Δ̂ = Θ̂ − Θ*`
satisfies `|||Δ̂_{𝕄̄⊥}|||_nuc ≤ 3 |||Δ̂_{𝕄̄}|||_nuc + 4 |||Θ*_{𝕄⊥}|||_nuc`.
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, §10.2.1, pp. 318–319 (PDF pp. 338–339), Eq. (10.15); `λ_n > 0` from (9.3), p. 260 (PDF p. 280).

Formalization Note: generalizations of the book's statement: (i) the book's convex
differentiable `L_n` with gradient `∇L_n(Θ*)` (with respect to the trace inner product) is
replaced by any `L` with a subgradient `G` at `Θ*`; (ii) the book's `𝕄 = 𝕄(𝕌ʳ, 𝕍ʳ)` (top `r`
singular subspaces of `Θ*`) is replaced by any pair `𝕌`, `𝕍`. Projections are `projMbarPerp`,
`projMbar`, `projMperp` (Frobenius-orthogonal). -/
theorem cone_constraint_nuclear {d₁ d₂ : ℕ}
    (L : Matrix (Fin d₁) (Fin d₂) ℝ → ℝ) (Θstar G : Matrix (Fin d₁) (Fin d₂) ℝ)
    (hG : ∀ Δ : Matrix (Fin d₁) (Fin d₂) ℝ, L Θstar + traceInner G Δ ≤ L (Θstar + Δ))
    (lam : ℝ) (hlam : 0 < lam) (hlamG : 2 * opNorm2 G ≤ lam)
    (Θhat : Matrix (Fin d₁) (Fin d₂) ℝ)
    (hmin : ∀ Θ : Matrix (Fin d₁) (Fin d₂) ℝ, L Θhat + lam * nucNorm Θhat ≤ L Θ + lam * nucNorm Θ)
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁))) (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂))) :
    nucNorm (projMbarPerp U V (Θhat - Θstar)) ≤
      3 * nucNorm (projMbar U V (Θhat - Θstar)) + 4 * nucNorm (projMperp U V Θstar) := by sorry

end WainwrightHDS.NucNorm
