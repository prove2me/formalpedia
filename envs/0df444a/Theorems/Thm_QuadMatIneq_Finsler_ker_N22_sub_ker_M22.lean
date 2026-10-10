-- Prove2me | Theorems.Thm_QuadMatIneq_Finsler_ker_N22_sub_ker_M22
-- name    : QuadMatIneq.Finsler.ker_N22_sub_ker_M22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:14:29.858127+00:00
-- url     : https://prove2.me/theorems/72fdd286-e2ab-46fa-a7db-b2a167e57ea3
-- title:
--   §4.3, proof of Theorem 4.8, p. 12 — if $\mathcal Z_r^0(N)\subseteq\mathcal Z_r(M)$, then $\ker N_{22}\subseteq\ker M_{22}$
-- statement:
--   Let $q\geqslant1$ and $r\geqslant0$, and let $M,N\in\boldsymbol\Pi_{q,r}$ be partitioned as in (4.1), with $N\,|\,N_{22}=0$. Suppose that every $Z\in\mathbb R^{r\times q}$ with $\begin{bmatrix}I\\ Z\end{bmatrix}^\top N\begin{bmatrix}I\\ Z\end{bmatrix}=0$ satisfies $\begin{bmatrix}I\\ Z\end{bmatrix}^\top M\begin{bmatrix}I\\ Z\end{bmatrix}\geqslant0$, i.e. $\mathcal Z_r^0(N)\subseteq\mathcal Z_r(M)$. Then
--   $$\ker N_{22}\subseteq\ker M_{22}.$$
--
--   This is the first step of the "only if" direction of Matrix Finsler's lemma (Theorem 4.8): it transfers the kernel structure of $N_{22}$ to $M_{22}$, which is what later allows a large multiplier $\alpha$ to dominate.
--
--   **Formalization Note** The hypothesis $q\geqslant1$ (`Nonempty ι`) is the paper's implicit one: the proof picks a nonzero $\eta\in\mathbb R^q$, and for $q=0$ the claim fails ($r=1$, $N=[0]$, $M=[-1]$). The hypotheses $N\in\boldsymbol\Pi_{q,r}$ and $N\,|\,N_{22}=0$ are those of Theorem 4.8; they make $\mathcal Z_r^0(N)$ nonempty, so the inclusion is not vacuous.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, §4.3, proof of Theorem 4.8, p. 12, display (4.5) and the sentence following it

import Mathlib
import Definitions.Def_QuadMatIneq_Finsler_QMI

namespace QuadMatIneq.Finsler
open Matrix QuadMatIneq.Basic
theorem ker_N22_sub_ker_M22 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [Nonempty ι]
    (M N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hM : InPi M) (hN : InPi N) (hNs : schur N = 0)
    (hsub : ZZero N ⊆ ZSet M) :
    ∀ v : κ → ℝ, N.toBlocks₂₂ *ᵥ v = 0 → M.toBlocks₂₂ *ᵥ v = 0 := by sorry
end QuadMatIneq.Finsler
