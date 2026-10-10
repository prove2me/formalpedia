-- Prove2me | Theorems.Thm_QuadMatIneq_Stabilization_theorem_4_11
-- name    : QuadMatIneq.Stabilization.theorem_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:13:36.212305+00:00
-- url     : https://prove2.me/theorems/eebee928-7635-4c44-aee8-0f47f0ff63cb
-- title:
--   Theorem 4.11 (Strict matrix S-lemma with α and β) — under N ∈ 𝚷_{q,r}, M₂₂ ⩽ 0 and a positive eigenvalue of N, 𝒵_r(N) ⊆ 𝒵_r^+(M) iff (4.9)
-- statement:
--   Let $M,N\in\mathbb{S}^{q+r}$, and consider, for scalars $\alpha,\beta$, the inequality
--   $$M-\alpha N\geqslant\begin{bmatrix}\beta I_q&0\\0&0_{r\times r}\end{bmatrix}. \tag{4.9}$$
--
--   1. If (4.9) holds for some $\alpha\geqslant 0$ and $\beta>0$, then $\mathcal Z_r(N)\subseteq\mathcal Z_r^+(M)$.
--   2. If moreover $N\in\boldsymbol\Pi_{q,r}$, $M_{22}\leqslant 0$ and $N$ has at least one positive eigenvalue, then $\mathcal Z_r(N)\subseteq\mathcal Z_r^+(M)$ if and only if (4.9) holds for some $\alpha\geqslant 0$ and $\beta>0$.
--
--   This version of the strict matrix S-lemma drops the requirement $N_{22}<0$ at the price of a second multiplier $\beta$ and the sign condition $M_{22}\leqslant 0$.
--
--
--   **Formalization Note** Matrices $M,N\in\mathbb{S}^{q+r}$ are real matrices indexed by `ι ⊕ κ` with $q=|\iota|$, $r=|\kappa|$ (the first block is $q\times q$, the second $r\times r$); "$\in\mathbb{S}$" is `IsHermitian`, $A\geqslant 0$ is `PosSemidef` and $A>0$ is `PosDef` (both include symmetry, as in §1.1 of the paper); $\mathcal Z_r(\cdot)$, $\mathcal Z_r^+(\cdot)$, $\mathcal Z_r^0(\cdot)$ and $\boldsymbol\Pi_{q,r}$ are `ZSet`, `ZPlus`, `ZZero`, `InPi` of the definitions item `QuadMatIneq.Stabilization.QMI`.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, Theorem 4.11, p. 13, (4.9)

import Mathlib
import Definitions.Def_QuadMatIneq_Stabilization_QMI

open Matrix

namespace QuadMatIneq.Stabilization

/-- Theorem 4.11 (Strict matrix S-lemma with α and β), p. 13. Inequality (4.9) is
`M − αN ⩾ [βI 0; 0 0]`, with `βI` of size `q × q` and the zero block `r × r`. -/
theorem theorem_4_11 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hM : M.IsHermitian) (hN : N.IsHermitian) :
    ((∃ α β : ℝ, 0 ≤ α ∧ 0 < β ∧
        (M - α • N - Matrix.fromBlocks (β • (1 : Matrix ι ι ℝ)) 0 0 0).PosSemidef) →
      ZSet N ⊆ ZPlus M) ∧
    (InPi N → (-M.toBlocks₂₂).PosSemidef → (∃ i, 0 < hN.eigenvalues i) →
      (ZSet N ⊆ ZPlus M ↔
        ∃ α β : ℝ, 0 ≤ α ∧ 0 < β ∧
          (M - α • N - Matrix.fromBlocks (β • (1 : Matrix ι ι ℝ)) 0 0 0).PosSemidef)) := by sorry

end QuadMatIneq.Stabilization
