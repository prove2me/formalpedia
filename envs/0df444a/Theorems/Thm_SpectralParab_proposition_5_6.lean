-- Prove2me | Theorems.Thm_SpectralParab_proposition_5_6
-- name    : SpectralParab.proposition_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:46:44.359497+00:00
-- url     : https://prove2.me/theorems/2e88ae37-eb4d-40e3-901a-7f6e91b7bccc
-- title:
--   Proposition 5.6: a block-sorted minimizer $z$ in (5.14) and a matrix $\widehat W$ with $\lambda''(X;H,\widehat W)=z$
-- statement:
--   Let $g=\theta\circ\lambda$ with $\theta$ symmetric (1.1) be lsc and convex, $Y\in\partial g(X)$ and $H\in K_g(X,Y)$. If $\theta$ is parabolically regular at $\lambda(X)$ for $\lambda(Y)$, then
--
--   1. there is $z\in\mathbb R^n$, written as in (5.13) with each piece $y_{\beta^m_i}$ nonincreasing, such that
--   $$\mathrm d^2\theta(\lambda(X),\lambda(Y))(\lambda'(X;H))=\mathrm d^2\theta(\lambda(X))(\lambda'(X;H)\,|\,z)-\langle\lambda(Y),z\rangle;\tag{5.14}$$
--   2. there is $\widehat W\in\mathbf S^n$ with $\lambda''(X;H,\widehat W)=z$, for this $z$.
--
--   Differences from the source:
--   - encoding: z = (y_{β^1_1},…,y_{β^r_{ρ_r}}) with every y_{β^m_i} ∈ ℝ↓^{|β^m_i|} → z_j ≤ z_i whenever i ≤ j, λ_i(X) = λ_j(X) and λ′_i(X;H) = λ′_j(X;H); reason: the β^m_i are the runs of equal λ′(X;H) inside α_m (by (2.9)), so both say z is nonincreasing on each β-block
--   - encoding: Definition 5.1 is stated for a convex f and v̄ ∈ ∂f(x̄) → ParabRegularAt carries neither condition; ParabRegular quantifies over v̄ ∈ subdiff; reason: every use supplies convexity and v̄ ∈ ∂f(x̄) as hypotheses or they follow from them (θ convex lsc by [4, Cor. 5.2.3], λ(Y) ∈ ∂θ(λ(X)) by Proposition 3.4)
--   - encoding: extended-real values in [−∞, ∞], quotients over f(x̄) finite → EReal, with the finite base subtracted as the real (f x̄).toReal; reason: Lean convention; on every instance where the paper's quotient is defined the two agree
--   - encoding: Sⁿ with ⟨X,Y⟩ = tr(XY), λ(X) nonincreasing eigenvalues, indices 1..n → SymMat (Fin n) (entrywise inner product, equal to tr(XY) on symmetric matrices), lam via eigVec, 0-based Fin n; reason: Lean convention; same objects, indices shifted by one
--   - encoding: λ′(X;H) and λ″(X;H,W) as one-sided limits → lamDir, lamDir2 via limUnder (𝓝[>] 0); reason: the limits exist (Corollary 2.3, stated as a milestone), so limUnder returns the paper's value
--   - encoding: lim sup_k ‖w_k − w‖/t_k < ∞ → ∃ C, ∀ k, ‖w_k − w‖ ≤ C t_k; reason: equivalent because t_k > 0
-- source:
--   A. Mohammadi, E. Sarabi, Parabolic Regularity of Spectral Functions, arXiv:2301.04240v3 (preprint basis), https://arxiv.org/abs/2301.04240v3, Proposition 5.6, (5.13)–(5.14), p.28

import Mathlib
import Definitions.Def_SpectralParab_Basic
import Definitions.Def_SpectralParab_ParabolicReg
import Definitions.Def_SpectralParab_SymMatSpace
import Definitions.Def_SpectralParab_EigBlocks

open Filter Topology Matrix Asymptotics
open scoped RealInnerProductSpace
open SunNLSDP.Equiv ModernConvex.Spectral

namespace SpectralParab

/-- arXiv:2301.04240v3, Proposition 5.6, p.28. Let `g = θ ∘ λ` ((1.1), `θ` symmetric) be lsc and
convex, `Y ∈ ∂g(X)` and `H ∈ K_g(X, Y)`. If `θ` is parabolically regular at `λ(X)` for `λ(Y)`,
then
(a) there is `z ∈ ℝⁿ` of the form (5.13) whose pieces `y_{β^m_i}` are nonincreasing, with
(5.14) `d²θ(λ(X), λ(Y))(λ'(X; H)) = d²θ(λ(X))(λ'(X; H) | z) − ⟨λ(Y), z⟩`; and
(b) there is `Ŵ ∈ Sⁿ` with `λ''(X; H, Ŵ) = z`, for this `z`.
**Formalization Note.** "`y_{β^m_i} ∈ ℝ↓^{|β^m_i|}`" is encoded as: `z_j ≤ z_i` whenever `i ≤ j`,
`λᵢ(X) = λⱼ(X)` and `λ'ᵢ(X; H) = λ'ⱼ(X; H)` (the blocks `β^m_i` are the level sets of `λ'(X;H)`
inside `α_m`, by (2.9)). (a) and (b) are about the same `z`. -/
theorem proposition_5_6 {n : ℕ} (θ : Rn n → EReal) (hθ : IsSymmetricFn θ)
    (hlsc : LowerSemicontinuous (specFn θ)) (hconv : IsConvexFn (specFn θ))
    (X Y : SymMat (Fin n)) (hY : Y ∈ subdiff (specFn θ) X)
    (H : SymMat (Fin n)) (hH : H ∈ critCone (specFn θ) X Y)
    (hreg : ParabRegularAt θ (lam X) (lam Y)) :
    ∃ z : Rn n,
      (∀ i j : Fin n, i ≤ j → lam X i = lam X j → lamDir X H i = lamDir X H j → z j ≤ z i) ∧
      secondSubderiv θ (lam X) (lam Y) (lamDir X H) =
        parabSubderiv θ (lam X) (lamDir X H) z - ((⟪lam Y, z⟫ : ℝ) : EReal) ∧
      ∃ What : SymMat (Fin n), lamDir2 X H What = z := by sorry

end SpectralParab
