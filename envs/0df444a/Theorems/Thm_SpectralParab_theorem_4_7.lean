-- Prove2me | Theorems.Thm_SpectralParab_theorem_4_7
-- name    : SpectralParab.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:46:48.023332+00:00
-- url     : https://prove2.me/theorems/efa89343-b99a-44a8-adc4-4788a86e7d11
-- title:
--   Theorem 4.7: parabolic epi-differentiability and the parabolic subderivative chain rule (4.15)–(4.16) for spectral functions
-- statement:
--   Let $\theta:\mathbb R^n\to\overline{\mathbb R}$ be symmetric and locally Lipschitz continuous relative to its domain, and $X\in\mathbf S^n$ with $(\theta\circ\lambda)(X)$ finite.
--
--   1. If $H\in T_{\operatorname{dom}(\theta\circ\lambda)}(X)$ and $\theta$ is parabolically epi-differentiable at $\lambda(X)$ for $\lambda'(X;H)$, then $\theta\circ\lambda$ is parabolically epi-differentiable at $X$ for $H$, and for every $W\in\mathbf S^n$
--   $$\mathrm d^2(\theta\circ\lambda)(X)(H\,|\,W)=\mathrm d^2\theta(\lambda(X))\big(\lambda'(X;H)\,|\,\lambda''(X;H,W)\big),\tag{4.15}$$
--   $$\operatorname{dom}\mathrm d^2(\theta\circ\lambda)(X)(H\,|\,\cdot)=T^2_{\operatorname{dom}(\theta\circ\lambda)}(X,H).\tag{4.16}$$
--   Moreover, if $\theta$ is lsc and convex, $W\mapsto\mathrm d^2(\theta\circ\lambda)(X)(H|W)$ is convex.
--   2. If $\theta\circ\lambda$ is parabolically epi-differentiable at $X$, then $\theta$ is parabolically epi-differentiable at $\lambda(X)$.
--
--   Differences from the source:
--   - encoding: extended-real values in [−∞, ∞], quotients over f(x̄) finite → EReal, with the finite base subtracted as the real (f x̄).toReal; reason: Lean convention; on every instance where the paper's quotient is defined the two agree
--   - encoding: Sⁿ with ⟨X,Y⟩ = tr(XY), λ(X) nonincreasing eigenvalues, indices 1..n → SymMat (Fin n) (entrywise inner product, equal to tr(XY) on symmetric matrices), lam via eigVec, 0-based Fin n; reason: Lean convention; same objects, indices shifted by one
--   - encoding: λ′(X;H) and λ″(X;H,W) as one-sided limits → lamDir, lamDir2 via limUnder (𝓝[>] 0); reason: the limits exist (Corollary 2.3, stated as a milestone), so limUnder returns the paper's value
--   - encoding: |f(x) − f(y)| ≤ ℓ‖x − y‖ on U ∩ C for an extended-real f → LocLipRel: f finite on U ∩ C, with the inequality on the real values (f x).toReal; reason: the printed inequality with y = x̄ already forces finiteness on U ∩ C; same functions
--   - encoding: the standing “f(x̄) finite, df(x̄)(w) finite” before the definition of parabolic epi-differentiability, p.17 → conjuncts of ParabEpiDiffAt; reason: the page assumes both before defining the notion; they exclude only undefined cases
-- source:
--   A. Mohammadi, E. Sarabi, Parabolic Regularity of Spectral Functions, arXiv:2301.04240v3 (preprint basis), https://arxiv.org/abs/2301.04240v3, Theorem 4.7, (4.15)–(4.16), p.18

import Mathlib
import Definitions.Def_SpectralParab_Basic
import Definitions.Def_SpectralParab_ParabolicReg
import Definitions.Def_SpectralParab_SymMatSpace
import Definitions.Def_SpectralParab_EigBlocks

open Filter Topology Matrix Asymptotics
open scoped RealInnerProductSpace
open SunNLSDP.Equiv ModernConvex.Spectral

namespace SpectralParab

/-- arXiv:2301.04240v3, Theorem 4.7, p.18 (parabolic subderivatives of spectral functions). Let
`θ : ℝⁿ → R̄` be symmetric and locally Lipschitz continuous relative to its domain, and
`X ∈ Sⁿ` with `(θ ∘ λ)(X)` finite.
(a) If `H ∈ T_{dom(θ∘λ)}(X)` and `θ` is parabolically epi-differentiable at `λ(X)` for `λ'(X; H)`,
then `θ ∘ λ` is parabolically epi-differentiable at `X` for `H`,
(4.15) `d²(θ∘λ)(X)(H | W) = d²θ(λ(X))(λ'(X; H) | λ''(X; H, W))` for every `W`, and
(4.16) `dom d²(θ∘λ)(X)(H | ·) = T²_{dom(θ∘λ)}(X, H)`; moreover, if `θ` is lsc and convex, the
function `W ↦ d²(θ∘λ)(X)(H | W)` is convex.
(b) If `θ ∘ λ` is parabolically epi-differentiable at `X`, then `θ` is parabolically
epi-differentiable at `λ(X)`. -/
theorem theorem_4_7 {n : ℕ} (θ : Rn n → EReal) (hθ : IsSymmetricFn θ) (hlip : LocLipOnDom θ)
    (X : SymMat (Fin n)) (hfin : specFn θ X ≠ ⊤ ∧ specFn θ X ≠ ⊥) :
    (∀ H ∈ tangentCone (dom (specFn θ)) X, ParabEpiDiffAt θ (lam X) (lamDir X H) →
      ParabEpiDiffAt (specFn θ) X H ∧
      (∀ W, parabSubderiv (specFn θ) X H W =
        parabSubderiv θ (lam X) (lamDir X H) (lamDir2 X H W)) ∧
      {W | parabSubderiv (specFn θ) X H W < ⊤} = secondTangentSet (dom (specFn θ)) X H ∧
      (LowerSemicontinuous θ → IsConvexFn θ →
        IsConvexFn (fun W => parabSubderiv (specFn θ) X H W))) ∧
    (ParabEpiDiff (specFn θ) X → ParabEpiDiff θ (lam X)) := by sorry

end SpectralParab
