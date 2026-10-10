-- Prove2me | Theorems.Thm_QuadMatIneq_Stabilization_theorem_4_12
-- name    : QuadMatIneq.Stabilization.theorem_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:14:23.417085+00:00
-- url     : https://prove2.me/theorems/9858296c-4373-4e1f-8b3b-5159844de0d2
-- title:
--   Theorem 4.12 (Strict matrix Finsler's lemma) — under N ∈ 𝚷_{q,r}, N|N₂₂ = 0, M₂₂ ⩽ 0 and q ⩾ 1, 𝒵_r^0(N) ⊆ 𝒵_r^+(M) iff (4.9)
-- statement:
--   Let $M,N\in\mathbb{S}^{q+r}$ and let (4.9) denote
--   $$M-\alpha N\geqslant\begin{bmatrix}\beta I_q&0\\0&0_{r\times r}\end{bmatrix}. \tag{4.9}$$
--
--   1. If (4.9) holds for some $\alpha\in\mathbb{R}$ and $\beta>0$, then $\mathcal Z_r^0(N)\subseteq\mathcal Z_r^+(M)$.
--   2. If moreover $q\geqslant 1$, $N\in\boldsymbol\Pi_{q,r}$, $N\,|\,N_{22}=0$ and $M_{22}\leqslant 0$, then $\mathcal Z_r^0(N)\subseteq\mathcal Z_r^+(M)$ if and only if (4.9) holds for some $\alpha\geqslant 0$ and $\beta>0$.
--
--   This is the strict matrix version of Finsler's lemma; together with Theorem 4.11 it yields Corollary 4.13, which needs no Slater condition.
--
--
--   **Formalization Note** Matrices $M,N\in\mathbb{S}^{q+r}$ are real matrices indexed by `ι ⊕ κ` with $q=|\iota|$, $r=|\kappa|$ (the first block is $q\times q$, the second $r\times r$); "$\in\mathbb{S}$" is `IsHermitian`, $A\geqslant 0$ is `PosSemidef` and $A>0$ is `PosDef` (both include symmetry, as in §1.1 of the paper); $\mathcal Z_r(\cdot)$, $\mathcal Z_r^+(\cdot)$, $\mathcal Z_r^0(\cdot)$ and $\boldsymbol\Pi_{q,r}$ are `ZSet`, `ZPlus`, `ZZero`, `InPi` of the definitions item `QuadMatIneq.Stabilization.QMI`. The hypothesis $q\geqslant 1$ (`Nonempty ι`) in the second statement is not printed in the paper but is necessary: for $q=0$, $r=1$, $N=[0]$, $M=[-1]$ all other hypotheses and the inclusion hold, yet (4.9) fails for every $\alpha$; the paper's proof picks a nonzero vector of $\mathbb{R}^q$.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, Theorem 4.12, p. 14, (4.9)

import Mathlib
import Definitions.Def_QuadMatIneq_Stabilization_QMI

open Matrix

namespace QuadMatIneq.Stabilization

/-- Theorem 4.12 (Strict matrix Finsler's lemma), p. 14. Inequality (4.9) is
`M − αN ⩾ [βI 0; 0 0]`. The second statement carries the added hypothesis `Nonempty ι`
(`q ⩾ 1`), without which it fails (`q = 0`, `r = 1`, `N = [0]`, `M = [−1]`). -/
theorem theorem_4_12 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hM : M.IsHermitian) (hN : N.IsHermitian) :
    ((∃ α β : ℝ, 0 < β ∧
        (M - α • N - Matrix.fromBlocks (β • (1 : Matrix ι ι ℝ)) 0 0 0).PosSemidef) →
      ZZero N ⊆ ZPlus M) ∧
    (Nonempty ι → InPi N → schur N = 0 → (-M.toBlocks₂₂).PosSemidef →
      (ZZero N ⊆ ZPlus M ↔
        ∃ α β : ℝ, 0 ≤ α ∧ 0 < β ∧
          (M - α • N - Matrix.fromBlocks (β • (1 : Matrix ι ι ℝ)) 0 0 0).PosSemidef)) := by sorry

end QuadMatIneq.Stabilization
