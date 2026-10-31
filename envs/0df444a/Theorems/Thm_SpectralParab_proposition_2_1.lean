-- Prove2me | Theorems.Thm_SpectralParab_proposition_2_1
-- name    : SpectralParab.proposition_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:46:04.426585+00:00
-- url     : https://prove2.me/theorems/6821fe49-f2c2-4a12-aad7-994852393f94
-- title:
--   Proposition 2.1: first-order expansions (2.7) and (2.8) of eigenvalue functions
-- statement:
--   Let $X\in\mathbf S^n$, $U\in O^n(X)$, and $\mu_1>\dots>\mu_r$ the distinct eigenvalues of $X$. For every index $i$, with $m$ such that $i\in\alpha_m$, as $H\to0$ in $\mathbf S^n$:
--   $$\lambda_i(X+H)=\lambda_i(X)+\lambda_{\ell_i}\big(U_{\alpha_m}^\top HU_{\alpha_m}+U_{\alpha_m}^\top H(\mu_mI-X)^\dagger HU_{\alpha_m}\big)+O(\|H\|^3),\tag{2.7}$$
--   $$\lambda_i(X+H)=\lambda_i(X)+\lambda_{\ell_i}\big(U_{\alpha_m}^\top HU_{\alpha_m}\big)+O(\|H\|^2).\tag{2.8}$$
--   These estimates, from Torki, are the analytic input of the lower estimate of Proposition 5.3.
--
--   **Formalization Note** $O(\cdot)$ is `=O[𝓝 0]` in $H\in\mathbf S^n$. $\mu_m=\lambda_i(X)$.
--
--   Differences from the source:
--   - encoding: Sⁿ with ⟨X,Y⟩ = tr(XY), λ(X) nonincreasing eigenvalues, indices 1..n → SymMat (Fin n) (entrywise inner product, equal to tr(XY) on symmetric matrices), lam via eigVec, 0-based Fin n; reason: Lean convention; same objects, indices shifted by one
--   - encoding: Z† the Moore–Penrose inverse → SunNLSDP.Equiv.pinv, the functional calculus cfc (·⁻¹) of a symmetric matrix; reason: every Z† in this statement has Z = µ_m I − X symmetric, and on symmetric matrices pinv satisfies the four Penrose equations
-- source:
--   A. Mohammadi, E. Sarabi, Parabolic Regularity of Spectral Functions, arXiv:2301.04240v3 (preprint basis), https://arxiv.org/abs/2301.04240v3, Proposition 2.1, (2.7)–(2.8), p.4

import Mathlib
import Definitions.Def_SpectralParab_Basic
import Definitions.Def_SpectralParab_ParabolicReg
import Definitions.Def_SpectralParab_SymMatSpace
import Definitions.Def_SpectralParab_EigBlocks

open Filter Topology Matrix Asymptotics
open scoped RealInnerProductSpace
open SunNLSDP.Equiv ModernConvex.Spectral

namespace SpectralParab

/-- arXiv:2301.04240v3, Proposition 2.1, p.4 (first-order expansion of eigenvalue functions, from
Torki [28]). Let `X ∈ Sⁿ`, `U ∈ Oⁿ(X)`, and `i` an index, lying in the block `α_m` of the
eigenvalue `μ_m = λᵢ(X)`. As `H → 0` in `Sⁿ`,
(2.7) `λᵢ(X + H) = λᵢ(X) + λ_{ℓᵢ}(U_{α_m}ᵀ H U_{α_m} + U_{α_m}ᵀ H (μ_m I − X)† H U_{α_m}) + O(‖H‖³)`, and
(2.8) `λᵢ(X + H) = λᵢ(X) + λ_{ℓᵢ}(U_{α_m}ᵀ H U_{α_m}) + O(‖H‖²)`.
**Formalization Note.** 0-based indices; `ell X i` is `ℓᵢ(X)`, `blockMat U X i M` is
`U_{α_m}ᵀ M U_{α_m}`, `shiftMat X i` is `μ_m I − X` and `pinv` its Moore–Penrose inverse.
The block matrices are symmetric, so `eigVec` is their ordered eigenvalue vector. -/
theorem proposition_2_1 {n : ℕ} (X : SymMat (Fin n)) (U : Matrix (Fin n) (Fin n) ℝ)
    (hU : U ∈ On X) (i : Fin n) :
    ((fun H : SymMat (Fin n) => lam (X + H) i - lam X i -
        eigVec (blockMat U X i (H.toMat + H.toMat * pinv (shiftMat X i) * H.toMat)) (ell X i))
        =O[𝓝 0] (fun H : SymMat (Fin n) => ‖H‖ ^ 3)) ∧
    ((fun H : SymMat (Fin n) => lam (X + H) i - lam X i - eigVec (blockMat U X i H.toMat) (ell X i))
        =O[𝓝 0] (fun H : SymMat (Fin n) => ‖H‖ ^ 2)) := by sorry

end SpectralParab
