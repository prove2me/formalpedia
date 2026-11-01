-- Prove2me | Theorems.Thm_RISRO_lemma_1_iteration_error
-- name    : RISRO.lemma_1_iteration_error
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:34:41.814598+00:00
-- url     : https://prove2.me/theorems/89914992-b290-4ee5-9980-dd1e84083959
-- title:
--   Lemma 1 — the least squares error is $(\mathcal L_t^*\mathcal A^*\mathcal A\mathcal L_t)^{-1}\mathcal L_t^*\mathcal A^*\epsilon^t$
-- statement:
--   Let $\mathcal A:\mathbb R^{p_1\times p_2}\to\mathbb R^n$, $\mathcal A(X)_i=\langle A_i,X\rangle$, and $y\in\mathbb R^n$. Let $U,V$ be orthonormal with orthonormal complements $U_\perp,V_\perp$, and let $\mathcal L_t$ be the operator of (9).
--    Let $\bar X$ be any target matrix, and put $\tilde B=U^\top\bar XV$, $\tilde D_1=U_\perp^\top\bar XV$, $\tilde D_2^\top=U^\top\bar XV_\perp$ and $\epsilon^t=\bar\epsilon+\mathcal A(P_{U_\perp}\bar XP_{V_\perp})$, $\bar\epsilon=y-\mathcal A(\bar X)$.
--
--   If $\mathcal L_t^*\mathcal A^*\mathcal A\mathcal L_t$ is invertible over $\mathrm{Ran}(\mathcal L_t^*)$, then every solution $(B,D_1,D_2)$ of (5) satisfies
--
--   $$
--   \begin{bmatrix} B-\tilde B & D_2^\top-\tilde D_2^\top\\ D_1-\tilde D_1 & 0\end{bmatrix}=(\mathcal L_t^*\mathcal A^*\mathcal A\mathcal L_t)^{-1}\mathcal L_t^*\mathcal A^*\epsilon^t
--   $$
--
--   and
--
--   $$
--   \|B-\tilde B\|_F^2+\sum_{k=1}^2\|D_k-\tilde D_k\|_F^2=\bigl\|(\mathcal L_t^*\mathcal A^*\mathcal A\mathcal L_t)^{-1}\mathcal L_t^*\mathcal A^*\epsilon^t\bigr\|_F^2 .
--   $$
--
--   This identity reduces the analysis of one RISRO step to the size of the right side.
--
--   Differences from the source:
--   - generalization: the data U^t, V^t, U_⊥^t, V_⊥^t of an iteration of RISRO → any orthonormal frames with orthonormal complements; reason: the proof uses only orthonormality; every iteration of every run supplies such frames
--   - encoding: matrices M ∈ Ran(L_t^*) with a zero bottom-right block → triples (W₀, W₁, W₂) with tripleNorm; reason: the same space with the same norm
--   - encoding: (L_t^* A^* A L_t)⁻¹ L_t^* A^* ϵ^t → the w with normalOp w = L_t^* A^* ϵ^t (IsErrorTriple); reason: the operator is injective here, so w is unique and equals the page's expression
-- source:
--   Luo, Huang, Li & Zhang, Recursive Importance Sketching for Rank Constrained Least Squares, arXiv:2011.08360v4, Lemma 1, displays (11)-(12), p.8

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic
import Definitions.Def_RISRO_IsFrame
import Definitions.Def_RISRO_Triple
import Definitions.Def_RISRO_tripleNorm
import Definitions.Def_RISRO_normalOp
import Definitions.Def_RISRO_IsLSMinimizer
import Definitions.Def_RISRO_IsErrorTriple

open HighDimStat.MatrixRank Matrix IRLSM.Convergence

namespace RISRO

/-- **Lemma 1 (Iteration Error Analysis for RISRO).** Let `X̄` be any target matrix. If
`L_t^* A^* A L_t` is invertible over `Ran(L_t^*)`, every solution `(B, D₁, D₂)` of (5) satisfies
(11), `[B - B̃, D₂ᵀ - D̃₂ᵀ; D₁ - D̃₁, 0] = (L_t^* A^* A L_t)⁻¹ L_t^* A^* ϵ^t`, and (12).

Luo, Huang, Li & Zhang, arXiv:2011.08360v4, Lemma 1, displays (11)–(12), p.8.

Formalization Notes: `(L_t^* A^* A L_t)⁻¹ L_t^* A^* ϵ^t` is the unique `w` of `IsErrorTriple`
(unique because `normalOp` is bijective). `B̃ = Uᵀ X̄ V`, `D̃₁ = U_⊥ᵀ X̄ V`, `D̃₂ᵀ = Uᵀ X̄ V_⊥`, display
(7), so `D̃₂ = V_⊥ᵀ X̄ᵀ U`. -/
theorem lemma_1_iteration_error {p₁ p₂ n r : ℕ} (A : Fin n → Matrix (Fin p₁) (Fin p₂) ℝ) (y : Fin n → ℝ)
    (Xbar : Matrix (Fin p₁) (Fin p₂) ℝ)
    (U : Matrix (Fin p₁) (Fin r) ℝ) (Uc : Matrix (Fin p₁) (Fin (p₁ - r)) ℝ)
    (V : Matrix (Fin p₂) (Fin r) ℝ) (Vc : Matrix (Fin p₂) (Fin (p₂ - r)) ℝ)
    (B : Matrix (Fin r) (Fin r) ℝ) (D₁ : Matrix (Fin (p₁ - r)) (Fin r) ℝ)
    (D₂ : Matrix (Fin (p₂ - r)) (Fin r) ℝ)
    (hU : IsFrame U Uc) (hV : IsFrame V Vc)
    (hinv : Function.Bijective (normalOp A U Uc V Vc))
    (hLS : IsLSMinimizer A y U Uc V Vc B D₁ D₂)
    (w : Triple p₁ p₂ r) (hw : IsErrorTriple A y Xbar U Uc V Vc w) :
    (B - Uᵀ * Xbar * V, D₁ - Ucᵀ * Xbar * V, D₂ᵀ - Uᵀ * Xbar * Vc) = w ∧
      frobeniusNorm (B - Uᵀ * Xbar * V) ^ 2 + frobeniusNorm (D₁ - Ucᵀ * Xbar * V) ^ 2 +
          frobeniusNorm (D₂ - Vcᵀ * Xbarᵀ * U) ^ 2 =
        tripleNorm w ^ 2 := by sorry

end RISRO
