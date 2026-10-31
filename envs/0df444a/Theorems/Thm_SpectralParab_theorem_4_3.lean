-- Prove2me | Theorems.Thm_SpectralParab_theorem_4_3
-- name    : SpectralParab.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:46:33.640005+00:00
-- url     : https://prove2.me/theorems/a21d0333-1d30-479a-9ad5-0bc28314c099
-- title:
--   Theorem 4.3: second-order tangent sets and parabolic derivability of spectral sets
-- statement:
--   Let $C=\{X\in\mathbf S^n\mid\lambda(X)\in\Theta\}$ with $\Theta$ symmetric (3.2), $X\in C$ and $H\in T_C(X)$. Then
--   $$T^2_C(X,H)=\{W\in\mathbf S^n\mid\lambda''(X;H,W)\in T^2_\Theta(\lambda(X),\lambda'(X;H))\},\tag{4.8}$$
--   and
--
--   1. if $\Theta$ is parabolically derivable at $\lambda(X)$ for $\lambda'(X;H)$, then $C$ is parabolically derivable at $X$ for $H$;
--   2. if $C$ is parabolically derivable at $X$ for every $H'\in T_C(X)$, then $\Theta$ is parabolically derivable at $\lambda(X)$ for every $v\in T_\Theta(\lambda(X))$.
--
--   No closedness of $C$ or $\Theta$ is assumed.
--
--   Differences from the source:
--   - reading: (b) “If the symmetric set C is parabolically derivable …” → C is the spectral set of the theorem; reason: C is defined by (3.2) as a spectral set; Θ is the symmetric set; “symmetric” is a slip
--   - encoding: Sⁿ with ⟨X,Y⟩ = tr(XY), λ(X) nonincreasing eigenvalues, indices 1..n → SymMat (Fin n) (entrywise inner product, equal to tr(XY) on symmetric matrices), lam via eigVec, 0-based Fin n; reason: Lean convention; same objects, indices shifted by one
--   - encoding: λ′(X;H) and λ″(X;H,W) as one-sided limits → lamDir, lamDir2 via limUnder (𝓝[>] 0); reason: the limits exist (Corollary 2.3, stated as a milestone), so limUnder returns the paper's value
--   - encoding: an arc ξ : [0, ε] → C → ξ : ℝ → E with ξ(t) ∈ C on [0, ε], no continuity required; reason: the page states no continuity, and the proof of Proposition 2.4 builds ξ from a bare o(t²) term; values outside [0, ε] are never read
-- source:
--   A. Mohammadi, E. Sarabi, Parabolic Regularity of Spectral Functions, arXiv:2301.04240v3 (preprint basis), https://arxiv.org/abs/2301.04240v3, Theorem 4.3, (4.8), p.14

import Mathlib
import Definitions.Def_SpectralParab_Basic
import Definitions.Def_SpectralParab_ParabolicReg
import Definitions.Def_SpectralParab_SymMatSpace
import Definitions.Def_SpectralParab_EigBlocks

open Filter Topology Matrix Asymptotics
open scoped RealInnerProductSpace
open SunNLSDP.Equiv ModernConvex.Spectral

namespace SpectralParab

/-- arXiv:2301.04240v3, Theorem 4.3, (4.8), p.14 (second-order tangent sets of spectral sets).
Let `C = {X ∈ Sⁿ | λ(X) ∈ Θ}` with `Θ` symmetric ((3.2)), `X ∈ C` and `H ∈ T_C(X)`. Then
(4.8) `T²_C(X, H) = {W ∈ Sⁿ | λ''(X; H, W) ∈ T²_Θ(λ(X), λ'(X; H))}`;
(a) if `Θ` is parabolically derivable at `λ(X)` for `λ'(X; H)`, then `C` is parabolically
derivable at `X` for `H`;
(b) if `C` is parabolically derivable at `X` for every `H' ∈ T_C(X)`, then `Θ` is parabolically
derivable at `λ(X)` for every `v ∈ T_Θ(λ(X))`.
**Formalization Note.** (b) prints "the symmetric set C"; `C` is the spectral set of the theorem
(reading). No closedness of `C` or `Θ` is assumed, as on the page. -/
theorem theorem_4_3 {n : ℕ} (Θ : Set (Rn n)) (hΘ : IsSymmetricSet Θ) (X : SymMat (Fin n))
    (hX : X ∈ specSet Θ) (H : SymMat (Fin n)) (hH : H ∈ tangentCone (specSet Θ) X) :
    secondTangentSet (specSet Θ) X H =
        {W | lamDir2 X H W ∈ secondTangentSet Θ (lam X) (lamDir X H)} ∧
    (ParabDerivable Θ (lam X) (lamDir X H) → ParabDerivable (specSet Θ) X H) ∧
    ((∀ H' ∈ tangentCone (specSet Θ) X, ParabDerivable (specSet Θ) X H') →
      ∀ v ∈ tangentCone Θ (lam X), ParabDerivable Θ (lam X) v) := by sorry

end SpectralParab
