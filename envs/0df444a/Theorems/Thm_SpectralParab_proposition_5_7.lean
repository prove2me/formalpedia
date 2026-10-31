-- Prove2me | Theorems.Thm_SpectralParab_proposition_5_7
-- name    : SpectralParab.proposition_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:47:10.223684+00:00
-- url     : https://prove2.me/theorems/4bbe9832-94f6-468e-8d6f-08b56e389578
-- title:
--   Proposition 5.7: $\operatorname{dom}\mathrm d^2g(X,Y)\subset K_g(X,Y)$, with equality under parabolic epi-differentiability
-- statement:
--   Let $g=\theta\circ\lambda$ with $\theta$ symmetric (1.1) be convex and $Y\in\partial g(X)$. Then
--   $$\operatorname{dom}\mathrm d^2g(X,Y)\subset K_g(X,Y),$$
--   with equality if, in addition, $g$ is parabolically epi-differentiable at $X$ for every $H\in K_g(X,Y)$. No lower semicontinuity is assumed.
--
--   Differences from the source:
--   - encoding: extended-real values in [−∞, ∞], quotients over f(x̄) finite → EReal, with the finite base subtracted as the real (f x̄).toReal; reason: Lean convention; on every instance where the paper's quotient is defined the two agree
--   - encoding: Sⁿ with ⟨X,Y⟩ = tr(XY), λ(X) nonincreasing eigenvalues, indices 1..n → SymMat (Fin n) (entrywise inner product, equal to tr(XY) on symmetric matrices), lam via eigVec, 0-based Fin n; reason: Lean convention; same objects, indices shifted by one
--   - encoding: the standing “f(x̄) finite, df(x̄)(w) finite” before the definition of parabolic epi-differentiability, p.17 → conjuncts of ParabEpiDiffAt; reason: the page assumes both before defining the notion; they exclude only undefined cases
-- source:
--   A. Mohammadi, E. Sarabi, Parabolic Regularity of Spectral Functions, arXiv:2301.04240v3 (preprint basis), https://arxiv.org/abs/2301.04240v3, Proposition 5.7, p.30

import Mathlib
import Definitions.Def_SpectralParab_Basic
import Definitions.Def_SpectralParab_ParabolicReg
import Definitions.Def_SpectralParab_SymMatSpace
import Definitions.Def_SpectralParab_EigBlocks

open Filter Topology Matrix Asymptotics
open scoped RealInnerProductSpace
open SunNLSDP.Equiv ModernConvex.Spectral

namespace SpectralParab

/-- arXiv:2301.04240v3, Proposition 5.7, p.30. Let `g = θ ∘ λ` ((1.1), `θ` symmetric) be convex and
`Y ∈ ∂g(X)`. Then `dom d²g(X, Y) ⊂ K_g(X, Y)`, with equality if, in addition, `g` is
parabolically epi-differentiable at `X` for every `H ∈ K_g(X, Y)`.
**Formalization Note.** No lower semicontinuity is assumed, as on the page. -/
theorem proposition_5_7 {n : ℕ} (θ : Rn n → EReal) (hθ : IsSymmetricFn θ)
    (hconv : IsConvexFn (specFn θ)) (X Y : SymMat (Fin n)) (hY : Y ∈ subdiff (specFn θ) X) :
    {H | secondSubderiv (specFn θ) X Y H < ⊤} ⊆ critCone (specFn θ) X Y ∧
    ((∀ H ∈ critCone (specFn θ) X Y, ParabEpiDiffAt (specFn θ) X H) →
      {H | secondSubderiv (specFn θ) X Y H < ⊤} = critCone (specFn θ) X Y) := by sorry

end SpectralParab
