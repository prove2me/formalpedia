-- Prove2me | Theorems.Thm_SpectralParab_proposition_4_8
-- name    : SpectralParab.proposition_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:47:15.20669+00:00
-- url     : https://prove2.me/theorems/a78d8d0a-1af0-4439-ac7a-a363778ca26b
-- title:
--   Proposition 4.8: the parabolic subderivative of $\theta$ is symmetric with respect to $\mathbf P^n_{X,H}$
-- statement:
--   Let $\theta:\mathbb R^n\to\overline{\mathbb R}$ be symmetric, $X\in\mathbf S^n$ with $\theta(\lambda(X))$ finite, and $H\in\mathbf S^n$ with $\mathrm d\theta(\lambda(X))(\lambda'(X;H))$ finite. For every $w\in\mathbb R^n$ and every $Q\in\mathbf P^n_{X,H}$,
--   $$\mathrm d^2\theta(\lambda(X))\big(\lambda'(X;H)\,|\,Qw\big)=\mathrm d^2\theta(\lambda(X))\big(\lambda'(X;H)\,|\,w\big).$$
--   This symmetry lets Proposition 5.6 sort the minimizer $z$ inside each block $\beta^m_j$.
--
--   Differences from the source:
--   - encoding: Pⁿ_{X,H}: block-diagonal permutation matrices Diag(B^1_1,…,B^r_{ρ_r}) → permutations σ with λ(X)∘σ = λ(X) and λ′(X;H)∘σ = λ′(X;H), acting by x ↦ x∘σ; reason: by (2.9) the level sets of λ′(X;H) inside α_m are the β^m_j, so the two sets coincide
--   - encoding: extended-real values in [−∞, ∞], quotients over f(x̄) finite → EReal, with the finite base subtracted as the real (f x̄).toReal; reason: Lean convention; on every instance where the paper's quotient is defined the two agree
--   - encoding: λ′(X;H) and λ″(X;H,W) as one-sided limits → lamDir, lamDir2 via limUnder (𝓝[>] 0); reason: the limits exist (Corollary 2.3, stated as a milestone), so limUnder returns the paper's value
--   - encoding: Sⁿ with ⟨X,Y⟩ = tr(XY), λ(X) nonincreasing eigenvalues, indices 1..n → SymMat (Fin n) (entrywise inner product, equal to tr(XY) on symmetric matrices), lam via eigVec, 0-based Fin n; reason: Lean convention; same objects, indices shifted by one
-- source:
--   A. Mohammadi, E. Sarabi, Parabolic Regularity of Spectral Functions, arXiv:2301.04240v3 (preprint basis), https://arxiv.org/abs/2301.04240v3, Proposition 4.8, p.21

import Mathlib
import Definitions.Def_SpectralParab_Basic
import Definitions.Def_SpectralParab_ParabolicReg
import Definitions.Def_SpectralParab_SymMatSpace
import Definitions.Def_SpectralParab_EigBlocks

open Filter Topology Matrix Asymptotics
open scoped RealInnerProductSpace
open SunNLSDP.Equiv ModernConvex.Spectral

namespace SpectralParab

/-- arXiv:2301.04240v3, Proposition 4.8, p.21. Let `θ : ℝⁿ → R̄` be symmetric, `X ∈ Sⁿ` with
`θ(λ(X))` finite and `H ∈ Sⁿ` with `dθ(λ(X))(λ'(X; H))` finite. For every `w ∈ ℝⁿ` and every
permutation matrix `Q ∈ Pⁿ_{X,H}`,
`d²θ(λ(X))(λ'(X; H) | Qw) = d²θ(λ(X))(λ'(X; H) | w)`.
**Formalization Note.** `Pⁿ_{X,H}` is `PnXH X H`, the permutations fixing `λ(X)` and `λ'(X; H)`
(see its definition); `Qw` is `permute σ w`. -/
theorem proposition_4_8 {n : ℕ} (θ : Rn n → EReal) (hθ : IsSymmetricFn θ) (X H : SymMat (Fin n))
    (hfin : θ (lam X) ≠ ⊤ ∧ θ (lam X) ≠ ⊥)
    (hdfin : subderiv θ (lam X) (lamDir X H) ≠ ⊤ ∧ subderiv θ (lam X) (lamDir X H) ≠ ⊥)
    (w : Rn n) (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ PnXH X H) :
    parabSubderiv θ (lam X) (lamDir X H) (permute σ w) =
      parabSubderiv θ (lam X) (lamDir X H) w := by sorry

end SpectralParab
