-- Prove2me | Theorems.Thm_SpectralParab_theorem_5_8
-- name    : SpectralParab.theorem_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:46:40.638969+00:00
-- url     : https://prove2.me/theorems/001181ae-a9ad-478d-9087-663ca9168267
-- title:
--   Theorem 5.8: parabolic regularity of spectral functions and the second subderivative formula
-- statement:
--   Let $\theta:\mathbb R^n\to\overline{\mathbb R}$ be symmetric and let the spectral function $g=\theta\circ\lambda$ of (1.1) be locally Lipschitz continuous with respect to its domain, lower semicontinuous and convex. Let $X\in\mathbf S^n$ have distinct eigenvalues $\mu_1>\dots>\mu_r$, with blocks $\alpha_m$ as in (2.4).
--
--   1. (a) If $Y\in\partial g(X)$ and $\theta$ is parabolically regular at $\lambda(X)$ for $\lambda(Y)$ and parabolically epi-differentiable at $\lambda(X)$, then $g$ is parabolically regular at $X$ for $Y$, and for every $H\in K_g(X,Y)$ and every $U\in O^n(X)\cap O^n(Y)$
--   $$\mathrm d^2g(X,Y)(H)=\mathrm d^2\theta(\lambda(X),\lambda(Y))(\lambda'(X;H))+2\sum_{m=1}^r\big\langle\Lambda(Y)_{\alpha_m\alpha_m},U_{\alpha_m}^\top H(\mu_mI-X)^\dagger HU_{\alpha_m}\big\rangle,$$
--   where $\Lambda(Y)=\operatorname{Diag}(\lambda(Y))$ and $^\dagger$ is the Moore–Penrose inverse.
--   2. (b) If $g$ is parabolically epi-differentiable and parabolically regular at $X$, then $\theta$ is parabolically regular at $\lambda(X)$.
--
--   Together, (a) and (b) say that parabolic regularity passes between a convex spectral function and its symmetric function, and (a) computes the second subderivative of $g$, the quantity that governs second-order optimality conditions for matrix optimization problems.
--
--   **Formalization Note** Values in `EReal`, finite bases through `toReal`, and $\partial g(X)=\emptyset$ when $g(X)$ is not finite. $\mathbf S^n$ is `SymMat (Fin n)` with the trace inner product; $\lambda'$, $\lambda''$ are one-sided limits. $\theta$ symmetric is part of the representation (1.1), not an added hypothesis.
--
--   Differences from the source:
--   - reading: “U ∈ Oⁿ(X) ∩ Oⁿ(Y)” with no explicit quantifier → the conclusion holds for every U ∈ Oⁿ(X) ∩ Oⁿ(Y); reason: the proof works for an arbitrary such U; the universal reading is the stronger one
--   - encoding: Σ_m ⟨Λ(Y)_{α_mα_m}, U_{α_m}ᵀ H(µ_m I − X)†HU_{α_m}⟩ → curvSum X Y H U = Σ_i λ_i(Y)·(Uᵀ H(λ_i(X)I − X)† H U)_{ii}; reason: Λ(Y)_{α_mα_m} is diagonal and µ_m = λ_i(X) on α_m, so this regroups the same finite sum
--   - encoding: Definition 5.1 is stated for a convex f and v̄ ∈ ∂f(x̄) → ParabRegularAt carries neither condition; ParabRegular quantifies over v̄ ∈ subdiff; reason: every use supplies convexity and v̄ ∈ ∂f(x̄) as hypotheses or they follow from them (θ convex lsc by [4, Cor. 5.2.3], λ(Y) ∈ ∂θ(λ(X)) by Proposition 3.4)
--   - encoding: extended-real values in [−∞, ∞], quotients over f(x̄) finite → EReal, with the finite base subtracted as the real (f x̄).toReal; reason: Lean convention; on every instance where the paper's quotient is defined the two agree
--   - encoding: Sⁿ with ⟨X,Y⟩ = tr(XY), λ(X) nonincreasing eigenvalues, indices 1..n → SymMat (Fin n) (entrywise inner product, equal to tr(XY) on symmetric matrices), lam via eigVec, 0-based Fin n; reason: Lean convention; same objects, indices shifted by one
--   - encoding: λ′(X;H) and λ″(X;H,W) as one-sided limits → lamDir, lamDir2 via limUnder (𝓝[>] 0); reason: the limits exist (Corollary 2.3, stated as a milestone), so limUnder returns the paper's value
--   - encoding: Z† the Moore–Penrose inverse → SunNLSDP.Equiv.pinv, the functional calculus cfc (·⁻¹) of a symmetric matrix; reason: every Z† in this statement has Z = µ_m I − X symmetric, and on symmetric matrices pinv satisfies the four Penrose equations
--   - encoding: |f(x) − f(y)| ≤ ℓ‖x − y‖ on U ∩ C for an extended-real f → LocLipRel: f finite on U ∩ C, with the inequality on the real values (f x).toReal; reason: the printed inequality with y = x̄ already forces finiteness on U ∩ C; same functions
--   - encoding: the standing “f(x̄) finite, df(x̄)(w) finite” before the definition of parabolic epi-differentiability, p.17 → conjuncts of ParabEpiDiffAt; reason: the page assumes both before defining the notion; they exclude only undefined cases
--   - encoding: lim sup_k ‖w_k − w‖/t_k < ∞ → ∃ C, ∀ k, ‖w_k − w‖ ≤ C t_k; reason: equivalent because t_k > 0
-- source:
--   A. Mohammadi, E. Sarabi, Parabolic Regularity of Spectral Functions, arXiv:2301.04240v3 (preprint basis), https://arxiv.org/abs/2301.04240v3, Theorem 5.8, p.30

import Mathlib
import Definitions.Def_SpectralParab_Basic
import Definitions.Def_SpectralParab_ParabolicReg
import Definitions.Def_SpectralParab_SymMatSpace
import Definitions.Def_SpectralParab_EigBlocks

open Filter Topology Matrix Asymptotics
open scoped RealInnerProductSpace
open SunNLSDP.Equiv ModernConvex.Spectral

namespace SpectralParab

/-- arXiv:2301.04240v3, Theorem 5.8, p.30 (parabolic regularity of spectral functions). Let the
spectral function `g = θ ∘ λ` of (1.1) (`θ` symmetric) be locally Lipschitz continuous with respect
to its domain, lsc and convex, and let `μ₁ > ⋯ > μ_r` be the distinct eigenvalues of `X ∈ Sⁿ`.
(a) If `Y ∈ ∂g(X)` and `θ` is parabolically regular at `λ(X)` for `λ(Y)` and parabolically
epi-differentiable at `λ(X)`, then `g` is parabolically regular at `X` for `Y`, and for every
`H ∈ K_g(X, Y)` (and every `U ∈ Oⁿ(X) ∩ Oⁿ(Y)`)
`d²g(X, Y)(H) = d²θ(λ(X), λ(Y))(λ'(X; H)) + 2 ∑_{m=1}^r ⟨Λ(Y)_{α_mα_m}, U_{α_m}ᵀ H (μ_m I − X)† H U_{α_m}⟩`.
(b) If `g` is parabolically epi-differentiable and parabolically regular at `X`, then `θ` is
parabolically regular at `λ(X)`.
**Formalization Note.** Values in `EReal`; finite bases enter through `toReal` and
`∂g(X) = ∅` when `g(X)` is not finite. `Sⁿ` is `SymMat (Fin n)` (trace inner product), `λ` is
`lam`, `λ'` and `λ''` are one-sided limits (`lamDir`, `lamDir2`). The sum is `curvSum X Y H U`,
the per-index regrouping `∑ᵢ λᵢ(Y) (Uᵀ H (λᵢ(X) I − X)† H U)ᵢᵢ` of the block sum, with `†` the
Moore–Penrose inverse. θ symmetric is part of (1.1). The formula is stated for every
`U ∈ Oⁿ(X) ∩ Oⁿ(Y)` (the page's "U ∈ Oⁿ(X) ∩ Oⁿ(Y)" read universally). -/
theorem theorem_5_8 {n : ℕ} (θ : Rn n → EReal) (hθ : IsSymmetricFn θ)
    (hlip : LocLipOnDom (specFn θ)) (hlsc : LowerSemicontinuous (specFn θ))
    (hconv : IsConvexFn (specFn θ)) (X : SymMat (Fin n)) :
    (∀ Y ∈ subdiff (specFn θ) X, ParabRegularAt θ (lam X) (lam Y) → ParabEpiDiff θ (lam X) →
      ParabRegularAt (specFn θ) X Y ∧
      ∀ H ∈ critCone (specFn θ) X Y, ∀ U : Matrix (Fin n) (Fin n) ℝ, U ∈ On X → U ∈ On Y →
        secondSubderiv (specFn θ) X Y H =
          secondSubderiv θ (lam X) (lam Y) (lamDir X H) + ((2 * curvSum X Y H U : ℝ) : EReal)) ∧
    (ParabEpiDiff (specFn θ) X → ParabRegular (specFn θ) X → ParabRegular θ (lam X)) := by sorry

end SpectralParab
