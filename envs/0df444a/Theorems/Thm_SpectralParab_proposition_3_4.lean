-- Prove2me | Theorems.Thm_SpectralParab_proposition_3_4
-- name    : SpectralParab.proposition_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:46:30.309125+00:00
-- url     : https://prove2.me/theorems/77c5c3f3-6037-40c9-986e-66bb86395043
-- title:
--   Proposition 3.4: subgradients of spectral functions via simultaneous ordered spectral decomposition
-- statement:
--   Let $\theta:\mathbb R^n\to\overline{\mathbb R}$ be proper, lower semicontinuous, convex and symmetric. For $X,Y\in\mathbf S^n$ the following are equivalent:
--
--   1. $Y\in\partial(\theta\circ\lambda)(X)$;
--   2. $\lambda(Y)\in\partial\theta(\lambda(X))$ and there is $U\in O^n(X)\cap O^n(Y)$, i.e. $X=U\Lambda(X)U^\top$ and $Y=U\Lambda(Y)U^\top$ with $\Lambda(\cdot)=\operatorname{Diag}(\lambda(\cdot))$.
--
--   This is Lewis's subdifferential formula, cited from [4, Theorem 5.2.4].
--
--   Differences from the source:
--   - encoding: extended-real values in [−∞, ∞], quotients over f(x̄) finite → EReal, with the finite base subtracted as the real (f x̄).toReal; reason: Lean convention; on every instance where the paper's quotient is defined the two agree
--   - encoding: Sⁿ with ⟨X,Y⟩ = tr(XY), λ(X) nonincreasing eigenvalues, indices 1..n → SymMat (Fin n) (entrywise inner product, equal to tr(XY) on symmetric matrices), lam via eigVec, 0-based Fin n; reason: Lean convention; same objects, indices shifted by one
-- source:
--   A. Mohammadi, E. Sarabi, Parabolic Regularity of Spectral Functions, arXiv:2301.04240v3 (preprint basis), https://arxiv.org/abs/2301.04240v3, Proposition 3.4, p.9

import Mathlib
import Definitions.Def_SpectralParab_Basic
import Definitions.Def_SpectralParab_ParabolicReg
import Definitions.Def_SpectralParab_SymMatSpace
import Definitions.Def_SpectralParab_EigBlocks

open Filter Topology Matrix Asymptotics
open scoped RealInnerProductSpace
open SunNLSDP.Equiv ModernConvex.Spectral

namespace SpectralParab

/-- arXiv:2301.04240v3, Proposition 3.4, p.9 (cited from [4, Theorem 5.2.4]). Let
`θ : ℝⁿ → R̄` be proper, lsc, convex and symmetric. Then `Y ∈ ∂(θ ∘ λ)(X)` iff
`λ(Y) ∈ ∂θ(λ(X))` and `X`, `Y` have a simultaneous ordered spectral decomposition: there is
`U ∈ Oⁿ(X) ∩ Oⁿ(Y)`, i.e. `X = U Λ(X) Uᵀ` and `Y = U Λ(Y) Uᵀ`.
**Formalization Note.** Proper: never `−∞` and not identically `+∞` (`IsProperFn`). -/
theorem proposition_3_4 {n : ℕ} (θ : Rn n → EReal) (hprop : IsProperFn θ)
    (hlsc : LowerSemicontinuous θ) (hconv : IsConvexFn θ) (hθ : IsSymmetricFn θ)
    (X Y : SymMat (Fin n)) :
    Y ∈ subdiff (specFn θ) X ↔
      lam Y ∈ subdiff θ (lam X) ∧ ∃ U : Matrix (Fin n) (Fin n) ℝ, U ∈ On X ∧ U ∈ On Y := by sorry

end SpectralParab
