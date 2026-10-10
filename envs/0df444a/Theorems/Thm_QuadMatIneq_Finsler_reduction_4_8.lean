-- Prove2me | Theorems.Thm_QuadMatIneq_Finsler_reduction_4_8
-- name    : QuadMatIneq.Finsler.reduction_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:13:14.629017+00:00
-- url     : https://prove2.me/theorems/937c6130-139d-459a-9b68-4271127bb347
-- title:
--   §4.3, proof of Theorem 4.8, p. 12, (4.8) — $T^\top(M-\alpha N)T\geqslant0$ iff $M_{22}-\alpha N_{22}-E\,\Theta^\dagger E^\top\geqslant0$
-- statement:
--   Let $M,N\in\boldsymbol\Pi_{q,r}$ be partitioned as in (4.1), with $N\,|\,N_{22}=0$, let $\Theta$ be as in (4.4) and $T$ as in (4.6), and assume $\ker\Theta\subseteq\ker(M\,|\,M_{22})$ and $\mathcal Z_r^0(N)\subseteq\mathcal Z_r(M)$. Then
--
--   1. $\ker\Theta=\ker(M\,|\,M_{22})$;
--   2. $\ker\Theta=\ker(M_{21}-M_{22}N_{22}^\dagger N_{21})$;
--   3. for every $\alpha\in\mathbb R$, $T^\top(M-\alpha N)T\geqslant0$ if and only if
--   $$M_{22}-\alpha N_{22}-\big(M_{21}-M_{22}N_{22}^\dagger N_{21}\big)\,\Theta^\dagger\,\big(M_{12}-N_{12}N_{22}^\dagger M_{22}\big)\geqslant0.\qquad(4.8)$$
--
--   This reduces the search for a multiplier $\alpha$ with $M-\alpha N\geqslant0$ to the $r\times r$ inequality (4.8), in which $\alpha$ enters only through $-\alpha N_{22}$.
--
--   **Formalization Note** Kernel equalities are stated pointwise on vectors $v\in\mathbb R^q$. The equivalence is claimed for every real $\alpha$, as on the page, which does not restrict $\alpha$ at this step.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, §4.3, proof of Theorem 4.8, p. 12, the paragraph ending in (4.8)

import Mathlib
import Definitions.Def_QuadMatIneq_Finsler_QMI

namespace QuadMatIneq.Finsler
open Matrix QuadMatIneq.Basic
theorem reduction_4_8 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hM : InPi M) (hN : InPi N) (hNs : schur N = 0)
    (hker : ∀ v : ι → ℝ, Theta M N *ᵥ v = 0 → schur M *ᵥ v = 0)
    (hsub : ZZero N ⊆ ZSet M) :
    (∀ v : ι → ℝ, Theta M N *ᵥ v = 0 ↔ schur M *ᵥ v = 0) ∧
    (∀ v : ι → ℝ, Theta M N *ᵥ v = 0 ↔
      (M.toBlocks₂₁ - M.toBlocks₂₂ * pinv N.toBlocks₂₂ * N.toBlocks₂₁) *ᵥ v = 0) ∧
    ∀ α : ℝ, ((Tmat N)ᵀ * (M - α • N) * Tmat N).PosSemidef ↔
      (M.toBlocks₂₂ - α • N.toBlocks₂₂ -
        (M.toBlocks₂₁ - M.toBlocks₂₂ * pinv N.toBlocks₂₂ * N.toBlocks₂₁) * pinv (Theta M N) *
          (M.toBlocks₁₂ - N.toBlocks₁₂ * pinv N.toBlocks₂₂ * M.toBlocks₂₂)).PosSemidef := by sorry
end QuadMatIneq.Finsler
