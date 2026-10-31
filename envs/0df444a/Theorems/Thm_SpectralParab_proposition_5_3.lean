-- Prove2me | Theorems.Thm_SpectralParab_proposition_5_3
-- name    : SpectralParab.proposition_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:46:40.682958+00:00
-- url     : https://prove2.me/theorems/aa0aecf0-deec-4c51-9c3d-528e83920a1c
-- title:
--   Proposition 5.3: lower estimate (5.1) for second subderivatives of spectral functions
-- statement:
--   Let $g=\theta\circ\lambda$ with $\theta$ symmetric (1.1) be lsc and convex, $Y\in\partial g(X)$, $\mu_1>\dots>\mu_r$ the distinct eigenvalues of $X$, and $U\in O^n(X)\cap O^n(Y)$. For every $H\in\mathbf S^n$,
--   $$\mathrm d^2g(X,Y)(H)\ge\mathrm d^2\theta(\lambda(X),\lambda(Y))(\lambda'(X;H))+2\sum_{m=1}^r\big\langle\Lambda(Y)_{\alpha_m\alpha_m},U_{\alpha_m}^\top H(\mu_mI-X)^\dagger HU_{\alpha_m}\big\rangle.\tag{5.1}$$
--   It is the lower half of the formula of Theorem 5.8(a).
--
--   Differences from the source:
--   - encoding: Σ_m ⟨Λ(Y)_{α_mα_m}, U_{α_m}ᵀ H(µ_m I − X)†HU_{α_m}⟩ → curvSum X Y H U = Σ_i λ_i(Y)·(Uᵀ H(λ_i(X)I − X)† H U)_{ii}; reason: Λ(Y)_{α_mα_m} is diagonal and µ_m = λ_i(X) on α_m, so this regroups the same finite sum
--   - encoding: extended-real values in [−∞, ∞], quotients over f(x̄) finite → EReal, with the finite base subtracted as the real (f x̄).toReal; reason: Lean convention; on every instance where the paper's quotient is defined the two agree
--   - encoding: Sⁿ with ⟨X,Y⟩ = tr(XY), λ(X) nonincreasing eigenvalues, indices 1..n → SymMat (Fin n) (entrywise inner product, equal to tr(XY) on symmetric matrices), lam via eigVec, 0-based Fin n; reason: Lean convention; same objects, indices shifted by one
--   - encoding: λ′(X;H) and λ″(X;H,W) as one-sided limits → lamDir, lamDir2 via limUnder (𝓝[>] 0); reason: the limits exist (Corollary 2.3, stated as a milestone), so limUnder returns the paper's value
--   - encoding: Z† the Moore–Penrose inverse → SunNLSDP.Equiv.pinv, the functional calculus cfc (·⁻¹) of a symmetric matrix; reason: every Z† in this statement has Z = µ_m I − X symmetric, and on symmetric matrices pinv satisfies the four Penrose equations
-- source:
--   A. Mohammadi, E. Sarabi, Parabolic Regularity of Spectral Functions, arXiv:2301.04240v3 (preprint basis), https://arxiv.org/abs/2301.04240v3, Proposition 5.3, (5.1), p.23

import Mathlib
import Definitions.Def_SpectralParab_Basic
import Definitions.Def_SpectralParab_ParabolicReg
import Definitions.Def_SpectralParab_SymMatSpace
import Definitions.Def_SpectralParab_EigBlocks

open Filter Topology Matrix Asymptotics
open scoped RealInnerProductSpace
open SunNLSDP.Equiv ModernConvex.Spectral

namespace SpectralParab

/-- arXiv:2301.04240v3, Proposition 5.3, (5.1), p.23 (lower estimate for second subderivatives).
Let `g = θ ∘ λ` ((1.1), `θ` symmetric) be lsc and convex, `Y ∈ ∂g(X)`, `μ₁ > ⋯ > μ_r` the
distinct eigenvalues of `X` and `U ∈ Oⁿ(X) ∩ Oⁿ(Y)`. For every `H ∈ Sⁿ`,
`d²g(X, Y)(H) ≥ d²θ(λ(X), λ(Y))(λ'(X; H)) + 2 ∑_{m=1}^r ⟨Λ(Y)_{α_mα_m}, U_{α_m}ᵀ H (μ_m I − X)† H U_{α_m}⟩`.
**Formalization Note.** The sum is `curvSum X Y H U` (per-index regrouping, see its definition),
a real number added in `EReal`. The statement holds for every `U ∈ Oⁿ(X) ∩ Oⁿ(Y)`. -/
theorem proposition_5_3 {n : ℕ} (θ : Rn n → EReal) (hθ : IsSymmetricFn θ)
    (hlsc : LowerSemicontinuous (specFn θ)) (hconv : IsConvexFn (specFn θ))
    (X Y : SymMat (Fin n)) (hY : Y ∈ subdiff (specFn θ) X)
    (U : Matrix (Fin n) (Fin n) ℝ) (hUX : U ∈ On X) (hUY : U ∈ On Y) (H : SymMat (Fin n)) :
    secondSubderiv θ (lam X) (lam Y) (lamDir X H) + ((2 * curvSum X Y H U : ℝ) : EReal) ≤
      secondSubderiv (specFn θ) X Y H := by sorry

end SpectralParab
