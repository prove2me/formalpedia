-- Prove2me | Theorems.Thm_SpectralParab_proposition_5_4
-- name    : SpectralParab.proposition_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:46:32.231128+00:00
-- url     : https://prove2.me/theorems/56a5208a-f5e2-4ff3-87b9-01461d89cf25
-- title:
--   Proposition 5.4: the critical cone of a convex spectral function
-- statement:
--   Let $g=\theta\circ\lambda$ with $\theta$ symmetric (1.1) be lsc and convex, $Y\in\partial g(X)$, and $U\in O^n(X)\cap O^n(Y)$. Then $H\in K_g(X,Y)$ if and only if
--
--   1. $\lambda'(X;H)\in K_\theta(\lambda(X),\lambda(Y))$, and
--   2. for every $m=1,\dots,r$ the matrices $\Lambda(Y)_{\alpha_m\alpha_m}$ and $U_{\alpha_m}^\top HU_{\alpha_m}$ have a simultaneous ordered spectral decomposition.
--
--   **Formalization Note** A block $\alpha_m$ is named by any of its indices, so "for every $m$" is "for every index $i$".
--
--   Differences from the source:
--   - reading: “U ∈ Oⁿ(X) ∩ Oⁿ(Y)” with no explicit quantifier → the conclusion holds for every U ∈ Oⁿ(X) ∩ Oⁿ(Y); reason: the proof works for an arbitrary such U; the universal reading is the stronger one
--   - encoding: extended-real values in [−∞, ∞], quotients over f(x̄) finite → EReal, with the finite base subtracted as the real (f x̄).toReal; reason: Lean convention; on every instance where the paper's quotient is defined the two agree
--   - encoding: Sⁿ with ⟨X,Y⟩ = tr(XY), λ(X) nonincreasing eigenvalues, indices 1..n → SymMat (Fin n) (entrywise inner product, equal to tr(XY) on symmetric matrices), lam via eigVec, 0-based Fin n; reason: Lean convention; same objects, indices shifted by one
--   - encoding: λ′(X;H) and λ″(X;H,W) as one-sided limits → lamDir, lamDir2 via limUnder (𝓝[>] 0); reason: the limits exist (Corollary 2.3, stated as a milestone), so limUnder returns the paper's value
--   - encoding: for any m = 1, …, r → ∀ i : Fin n, the block α_m being named by any index i in it; reason: the blocks partition the indices, so both quantifiers range over the same blocks
-- source:
--   A. Mohammadi, E. Sarabi, Parabolic Regularity of Spectral Functions, arXiv:2301.04240v3 (preprint basis), https://arxiv.org/abs/2301.04240v3, Proposition 5.4, p.24

import Mathlib
import Definitions.Def_SpectralParab_Basic
import Definitions.Def_SpectralParab_ParabolicReg
import Definitions.Def_SpectralParab_SymMatSpace
import Definitions.Def_SpectralParab_EigBlocks

open Filter Topology Matrix Asymptotics
open scoped RealInnerProductSpace
open SunNLSDP.Equiv ModernConvex.Spectral

namespace SpectralParab

/-- arXiv:2301.04240v3, Proposition 5.4, p.24 (critical cone of spectral functions). Let
`g = θ ∘ λ` ((1.1), `θ` symmetric) be lsc and convex and `Y ∈ ∂g(X)`. Then, for
`U ∈ Oⁿ(X) ∩ Oⁿ(Y)`, `H ∈ K_g(X, Y)` if and only if `λ'(X; H) ∈ K_θ(λ(X), λ(Y))` and, for every
block `α_m` of (2.4), the matrices `Λ(Y)_{α_mα_m}` and `U_{α_m}ᵀ H U_{α_m}` have a simultaneous
ordered spectral decomposition.
**Formalization Note.** The block `α_m` is named by any of its indices `i` (`∀ i` covers every
`m`). The statement is made for every `U ∈ Oⁿ(X) ∩ Oⁿ(Y)` (reading of the page's "and U ∈ …"). -/
theorem proposition_5_4 {n : ℕ} (θ : Rn n → EReal) (hθ : IsSymmetricFn θ)
    (hlsc : LowerSemicontinuous (specFn θ)) (hconv : IsConvexFn (specFn θ))
    (X Y : SymMat (Fin n)) (hY : Y ∈ subdiff (specFn θ) X)
    (U : Matrix (Fin n) (Fin n) ℝ) (hUX : U ∈ On X) (hUY : U ∈ On Y) (H : SymMat (Fin n)) :
    H ∈ critCone (specFn θ) X Y ↔
      lamDir X H ∈ critCone θ (lam X) (lam Y) ∧
        ∀ i : Fin n, SimOrdSpecDecomp (diagBlock X Y i) (blockMat U X i H.toMat) := by sorry

end SpectralParab
