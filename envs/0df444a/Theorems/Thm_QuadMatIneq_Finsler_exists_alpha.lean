-- Prove2me | Theorems.Thm_QuadMatIneq_Finsler_exists_alpha
-- name    : QuadMatIneq.Finsler.exists_alpha
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:12:58.588978+00:00
-- url     : https://prove2.me/theorems/2e0b43d6-73b5-4616-9882-524a4bb3007a
-- title:
--   §4.3, proof of Theorem 4.8, p. 13 — some $\alpha\geqslant0$ satisfies (4.8), hence $M-\alpha N\geqslant0$
-- statement:
--   Let $q\geqslant1$, let $M,N\in\boldsymbol\Pi_{q,r}$ be partitioned as in (4.1), with $N\,|\,N_{22}=0$, let $\Theta$ be as in (4.4), and assume $\ker\Theta\subseteq\ker(M\,|\,M_{22})$ and $\mathcal Z_r^0(N)\subseteq\mathcal Z_r(M)$. Then there exists $\alpha\geqslant0$ such that
--   $$M_{22}-\alpha N_{22}-\big(M_{21}-M_{22}N_{22}^\dagger N_{21}\big)\,\Theta^\dagger\,\big(M_{12}-N_{12}N_{22}^\dagger M_{22}\big)\geqslant0\qquad(4.8)$$
--   and, for the same $\alpha$,
--   $$M-\alpha N\geqslant0 .$$
--
--   This is the final step of the "only if" direction of Theorem 4.8.
--
--   **Formalization Note** The hypothesis $q\geqslant1$ (`Nonempty ι`) is the paper's implicit one, inherited from the step $\ker N_{22}\subseteq\ker M_{22}$ that this sentence uses; without it the claim fails ($q=0$, $r=1$, $N=[0]$, $M=[-1]$).
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, §4.3, proof of Theorem 4.8, p. 13, first paragraph

import Mathlib
import Definitions.Def_QuadMatIneq_Finsler_QMI

namespace QuadMatIneq.Finsler
open Matrix QuadMatIneq.Basic
theorem exists_alpha {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [Nonempty ι]
    (M N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hM : InPi M) (hN : InPi N) (hNs : schur N = 0)
    (hker : ∀ v : ι → ℝ, Theta M N *ᵥ v = 0 → schur M *ᵥ v = 0)
    (hsub : ZZero N ⊆ ZSet M) :
    ∃ α : ℝ, 0 ≤ α ∧
      (M.toBlocks₂₂ - α • N.toBlocks₂₂ -
        (M.toBlocks₂₁ - M.toBlocks₂₂ * pinv N.toBlocks₂₂ * N.toBlocks₂₁) * pinv (Theta M N) *
          (M.toBlocks₁₂ - N.toBlocks₁₂ * pinv N.toBlocks₂₂ * M.toBlocks₂₂)).PosSemidef ∧
      (M - α • N).PosSemidef := by sorry
end QuadMatIneq.Finsler
