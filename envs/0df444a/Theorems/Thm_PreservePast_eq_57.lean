-- Prove2me | Theorems.Thm_PreservePast_eq_57
-- name    : PreservePast.eq_57
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:40:32.403328+00:00
-- url     : https://prove2.me/theorems/fddcea88-9c83-4f7b-a23a-6ab7c70da5ea
-- title:
--   (57) — transferring the trace bound to a query
-- statement:
--   Let $F\in\mathbb R^{m\times k}$, $u\in\mathbb R^k$ a unit vector, $A=FF^\top$, $v=Fu$ and $M=A-vv^\top$. Let $p\in\mathbb R^m$ be a unit vector, $1\le r$, and let $V\subseteq\mathbb R^m$ be a subspace of dimension $L$ with orthonormal basis $y_1,\dots,y_L$, where $r+1\le L<m$. With
--   $$
--   \Delta_V=\mathcal K_L(A)-\operatorname{tr}(P_VA),\qquad \tau=\lambda_{L+1}(A),\qquad Q=V+\operatorname{span}\{p\},
--   $$
--   one has
--   $$
--   \Gamma_r(M;p,\mathbb R^m)-\Gamma_r(M;p,Q)\le2(\Delta_V+\tau).
--   $$
--   Here $P_V$ is the orthogonal projection onto $V$, so $\operatorname{tr}(P_VA)=\sum_jy_j^\top Ay_j$, and $\lambda_{L+1}(A)$ is the $(L+1)$-st largest eigenvalue.
--
--   The bound transfers a trace-capture guarantee for $A$ on $V$ to the penalized improvement available after a query has fixed the direction $p$.
--
--   **Formalization Note** $\lambda_{L+1}(A)=\mathcal K_{L+1}(A)-\mathcal K_L(A)$; $\Gamma_r$ uses $\mathcal K_{r-1}$, so $r\ge1$ is assumed.
--
--   Differences from the source:
--   - encoding: V a subspace of dimension L; tr(P_V A); λ_{L+1}(A) → V spanned by an orthonormal family Y of L vectors; Σ_j y_jᵀAy_j; 𝒦_{L+1}(A) − 𝒦_L(A); reason: the same objects; tr(P_V A) does not depend on the basis
--   - encoding: r unrestricted in the claim → 1 ≤ r; reason: Γ_r is undefined for r = 0 (𝒦_{r−1}); excludes only undefined cases
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §C.4, p.22 (PDF p.24), (57)

import Mathlib
import Definitions.Def_PreservePast_kyFanOn

open Matrix

namespace PreservePast

/-- **(57): transferring the trace bound to a query.** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §C.4, p.22 (PDF p.24): "Suppose
A = FF^⊤, v = Fu for unit u, M = A − vv^⊤, and V has dimension L with r + 1 ≤ L < m. With
Δ_V = 𝒦_L(A) − tr(P_V A), τ = λ_{L+1}(A) and Q = V + span{p}, we claim
Γ_r(M; p, ℝᵐ) − Γ_r(M; p, Q) ≤ 2(Δ_V + τ). (57)"

The `L`-dimensional subspace `V` is given by an orthonormal basis `Y`, so `tr(P_V A) = Σ_j y_jᵀ A y_j`;
`λ_{L+1}(A) = 𝒦_{L+1}(A) − 𝒦_L(A)` is the `(L+1)`-st largest eigenvalue of `A`; `p` is a unit vector.

**Formalization Note.** `F ∈ ℝ^{m×k}` for an arbitrary `k`; `r ≥ 1`, the response rank of the
section; `Γ_r` is `gammaR`, with `ℝᵐ = ⊤`. -/
theorem eq_57 {m k r L : ℕ} (F : Matrix (Fin m) (Fin k) ℝ) (u : Fin k → ℝ)
    (hu : ∑ i, u i ^ 2 = 1) (p : Fin m → ℝ) (hp : ∑ j, p j ^ 2 = 1) (Y : Fin L → Fin m → ℝ)
    (hY : IsOrthoFrameIn ⊤ Y) (hr1 : 1 ≤ r) (hrL : r + 1 ≤ L) (hLm : L < m) :
    let A : Matrix (Fin m) (Fin m) ℝ := F * F.transpose
    let v : Fin m → ℝ := F *ᵥ u
    let M : Matrix (Fin m) (Fin m) ℝ := A - Matrix.vecMulVec v v
    let ΔV : ℝ := kyFanOn L A ⊤ - ∑ j, Y j ⬝ᵥ (A *ᵥ Y j)
    let τ : ℝ := kyFanOn (L + 1) A ⊤ - kyFanOn L A ⊤
    let Q : Submodule ℝ (Fin m → ℝ) := Submodule.span ℝ (Set.range Y) ⊔ Submodule.span ℝ {p}
    gammaR r M p ⊤ - gammaR r M p Q ≤ 2 * (ΔV + τ) := by sorry

end PreservePast
