-- Prove2me | Theorems.Thm_SpectralParab_theorem_3_5
-- name    : SpectralParab.theorem_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:46:16.032179+00:00
-- url     : https://prove2.me/theorems/9a8b08c0-14b0-495a-a5c6-715486a4d91c
-- title:
--   Theorem 3.5: chain rule $\mathrm d(\theta\circ\lambda)(X)(H)=\mathrm d\theta(\lambda(X))(\lambda'(X;H))$
-- statement:
--   Let $\theta:\mathbb R^n\to\overline{\mathbb R}$ be symmetric and $X\in\mathbf S^n$ with $(\theta\circ\lambda)(X)$ finite. If either $\theta$ is lsc and convex with $\partial\theta(\lambda(X))\ne\emptyset$, or $\theta$ is locally Lipschitz continuous around $\lambda(X)$ relative to its domain, then for all $H\in\mathbf S^n$
--   $$\mathrm d(\theta\circ\lambda)(X)(H)=\mathrm d\theta(\lambda(X))(\lambda'(X;H)).\tag{3.8}$$
--
--   Differences from the source:
--   - encoding: extended-real values in [−∞, ∞], quotients over f(x̄) finite → EReal, with the finite base subtracted as the real (f x̄).toReal; reason: Lean convention; on every instance where the paper's quotient is defined the two agree
--   - encoding: Sⁿ with ⟨X,Y⟩ = tr(XY), λ(X) nonincreasing eigenvalues, indices 1..n → SymMat (Fin n) (entrywise inner product, equal to tr(XY) on symmetric matrices), lam via eigVec, 0-based Fin n; reason: Lean convention; same objects, indices shifted by one
--   - encoding: λ′(X;H) and λ″(X;H,W) as one-sided limits → lamDir, lamDir2 via limUnder (𝓝[>] 0); reason: the limits exist (Corollary 2.3, stated as a milestone), so limUnder returns the paper's value
--   - encoding: |f(x) − f(y)| ≤ ℓ‖x − y‖ on U ∩ C for an extended-real f → LocLipRel: f finite on U ∩ C, with the inequality on the real values (f x).toReal; reason: the printed inequality with y = x̄ already forces finiteness on U ∩ C; same functions
-- source:
--   A. Mohammadi, E. Sarabi, Parabolic Regularity of Spectral Functions, arXiv:2301.04240v3 (preprint basis), https://arxiv.org/abs/2301.04240v3, Theorem 3.5, (3.8), p.9

import Mathlib
import Definitions.Def_SpectralParab_Basic
import Definitions.Def_SpectralParab_ParabolicReg
import Definitions.Def_SpectralParab_SymMatSpace
import Definitions.Def_SpectralParab_EigBlocks

open Filter Topology Matrix Asymptotics
open scoped RealInnerProductSpace
open SunNLSDP.Equiv ModernConvex.Spectral

namespace SpectralParab

/-- arXiv:2301.04240v3, Theorem 3.5, (3.8), p.9 (subderivatives of spectral functions). Let
`θ : ℝⁿ → R̄` be symmetric and `X ∈ Sⁿ` with `(θ ∘ λ)(X)` finite. If `θ` is either lsc and convex
with `∂θ(λ(X)) ≠ ∅`, or locally Lipschitz continuous around `λ(X)` relative to its domain, then
for all `H ∈ Sⁿ`, `d(θ ∘ λ)(X)(H) = dθ(λ(X))(λ'(X; H))`. -/
theorem theorem_3_5 {n : ℕ} (θ : Rn n → EReal) (hθ : IsSymmetricFn θ) (X : SymMat (Fin n))
    (hfin : specFn θ X ≠ ⊤ ∧ specFn θ X ≠ ⊥)
    (hreg : (LowerSemicontinuous θ ∧ IsConvexFn θ ∧ (subdiff θ (lam X)).Nonempty) ∨
      LocLipRel θ (dom θ) (lam X)) (H : SymMat (Fin n)) :
    subderiv (specFn θ) X H = subderiv θ (lam X) (lamDir X H) := by sorry

end SpectralParab
