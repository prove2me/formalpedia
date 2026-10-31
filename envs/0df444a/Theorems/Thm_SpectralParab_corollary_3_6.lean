-- Prove2me | Theorems.Thm_SpectralParab_corollary_3_6
-- name    : SpectralParab.corollary_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:46:25.133473+00:00
-- url     : https://prove2.me/theorems/07c79739-6d5d-437a-ba5f-0281e318a4a4
-- title:
--   Corollary 3.6: tangent cone to spectral sets
-- statement:
--   Let $\Theta\subset\mathbb R^n$ be a symmetric set and $C=\{X\in\mathbf S^n\mid\lambda(X)\in\Theta\}$ the spectral set (3.2). For every $X\in C$,
--   $$T_C(X)=\{H\in\mathbf S^n\mid\lambda'(X;H)\in T_\Theta(\lambda(X))\}.$$
--
--   Differences from the source:
--   - encoding: Sⁿ with ⟨X,Y⟩ = tr(XY), λ(X) nonincreasing eigenvalues, indices 1..n → SymMat (Fin n) (entrywise inner product, equal to tr(XY) on symmetric matrices), lam via eigVec, 0-based Fin n; reason: Lean convention; same objects, indices shifted by one
--   - encoding: λ′(X;H) and λ″(X;H,W) as one-sided limits → lamDir, lamDir2 via limUnder (𝓝[>] 0); reason: the limits exist (Corollary 2.3, stated as a milestone), so limUnder returns the paper's value
-- source:
--   A. Mohammadi, E. Sarabi, Parabolic Regularity of Spectral Functions, arXiv:2301.04240v3 (preprint basis), https://arxiv.org/abs/2301.04240v3, Corollary 3.6, p.11

import Mathlib
import Definitions.Def_SpectralParab_Basic
import Definitions.Def_SpectralParab_ParabolicReg
import Definitions.Def_SpectralParab_SymMatSpace
import Definitions.Def_SpectralParab_EigBlocks

open Filter Topology Matrix Asymptotics
open scoped RealInnerProductSpace
open SunNLSDP.Equiv ModernConvex.Spectral

namespace SpectralParab

/-- arXiv:2301.04240v3, Corollary 3.6, p.11 (tangent cone to spectral sets). Let `C` be a spectral
set represented by (3.2), `C = {X ∈ Sⁿ | λ(X) ∈ Θ}` with `Θ` symmetric. For every `X ∈ C`,
`T_C(X) = {H ∈ Sⁿ | λ'(X; H) ∈ T_Θ(λ(X))}`. -/
theorem corollary_3_6 {n : ℕ} (Θ : Set (Rn n)) (hΘ : IsSymmetricSet Θ) (X : SymMat (Fin n))
    (hX : X ∈ specSet Θ) :
    tangentCone (specSet Θ) X = {H | lamDir X H ∈ tangentCone Θ (lam X)} := by sorry

end SpectralParab
