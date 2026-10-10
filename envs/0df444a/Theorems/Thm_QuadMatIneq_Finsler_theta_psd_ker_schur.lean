-- Prove2me | Theorems.Thm_QuadMatIneq_Finsler_theta_psd_ker_schur
-- name    : QuadMatIneq.Finsler.theta_psd_ker_schur
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:12:49.116516+00:00
-- url     : https://prove2.me/theorems/c11e2de5-e2dc-40bc-bb4a-6d8128d79cf2
-- title:
--   §4.3, proof of Theorem 4.8, p. 12 — $\Theta\geqslant0$ and $\ker(M|M_{22})=\ker\Theta\cap\ker(M_{21}-M_{22}N_{22}^\dagger N_{21})$
-- statement:
--   Let $M,N\in\boldsymbol\Pi_{q,r}$ be partitioned as in (4.1), with $N\,|\,N_{22}=0$, let $\Theta$ be as in (4.4), and suppose $\mathcal Z_r^0(N)\subseteq\mathcal Z_r(M)$. Then
--   $$\Theta\geqslant0$$
--   and
--   $$\ker(M\,|\,M_{22})=\ker\Theta\,\cap\,\ker\big(M_{21}-M_{22}N_{22}^\dagger N_{21}\big).$$
--
--   The first claim holds because $-N_{22}^\dagger N_{21}\in\mathcal Z_r^0(N)$; the kernel identity is the bridge between the hypothesis $\ker\Theta\subseteq\ker(M\,|\,M_{22})$ of Theorem 4.8 and the off-diagonal block of (4.6).
--
--   **Formalization Note** The kernel identity is stated pointwise: for every $v\in\mathbb R^q$, $(M\,|\,M_{22})v=0$ if and only if $\Theta v=0$ and $(M_{21}-M_{22}N_{22}^\dagger N_{21})v=0$.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, §4.3, proof of Theorem 4.8, p. 12, the sentence after (4.7b)

import Mathlib
import Definitions.Def_QuadMatIneq_Finsler_QMI

namespace QuadMatIneq.Finsler
open Matrix QuadMatIneq.Basic
theorem theta_psd_ker_schur {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hM : InPi M) (hN : InPi N) (hNs : schur N = 0)
    (hsub : ZZero N ⊆ ZSet M) :
    (Theta M N).PosSemidef ∧
    ∀ v : ι → ℝ, schur M *ᵥ v = 0 ↔
      (Theta M N *ᵥ v = 0 ∧
        (M.toBlocks₂₁ - M.toBlocks₂₂ * pinv N.toBlocks₂₂ * N.toBlocks₂₁) *ᵥ v = 0) := by sorry
end QuadMatIneq.Finsler
