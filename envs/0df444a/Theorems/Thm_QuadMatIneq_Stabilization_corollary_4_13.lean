-- Prove2me | Theorems.Thm_QuadMatIneq_Stabilization_corollary_4_13
-- name    : QuadMatIneq.Stabilization.corollary_4_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:13:33.017982+00:00
-- url     : https://prove2.me/theorems/85d8999b-d4d1-433c-94cb-593f93675c79
-- title:
--   Corollary 4.13 — for N ∈ 𝚷_{q,r}, M₂₂ ⩽ 0 and q ⩾ 1, 𝒵_r(N) ⊆ 𝒵_r^+(M) iff M − αN ⩾ diag(βI, 0) for some α ⩾ 0, β > 0
-- statement:
--   Let $M,N\in\mathbb{S}^{q+r}$ and let (4.9) denote
--   $$M-\alpha N\geqslant\begin{bmatrix}\beta I_q&0\\0&0_{r\times r}\end{bmatrix}. \tag{4.9}$$
--
--   1. If (4.9) holds for some $\alpha\geqslant 0$ and $\beta>0$, then $\mathcal Z_r(N)\subseteq\mathcal Z_r^+(M)$.
--   2. If moreover $q\geqslant 1$, $N\in\boldsymbol\Pi_{q,r}$ and $M_{22}\leqslant 0$, then $\mathcal Z_r(N)\subseteq\mathcal Z_r^+(M)$ if and only if (4.9) holds for some $\alpha\geqslant 0$ and $\beta>0$.
--
--   This combination of the strict matrix S-lemma and Finsler's lemma has no Slater condition on $N$; it is the result applied in the proof of Theorem 5.1.
--
--
--   **Formalization Note** Matrices $M,N\in\mathbb{S}^{q+r}$ are real matrices indexed by `ι ⊕ κ` with $q=|\iota|$, $r=|\kappa|$ (the first block is $q\times q$, the second $r\times r$); "$\in\mathbb{S}$" is `IsHermitian`, $A\geqslant 0$ is `PosSemidef` and $A>0$ is `PosDef` (both include symmetry, as in §1.1 of the paper); $\mathcal Z_r(\cdot)$, $\mathcal Z_r^+(\cdot)$, $\mathcal Z_r^0(\cdot)$ and $\boldsymbol\Pi_{q,r}$ are `ZSet`, `ZPlus`, `ZZero`, `InPi` of the definitions item `QuadMatIneq.Stabilization.QMI`. The hypothesis $q\geqslant 1$ (`Nonempty ι`) in the second statement is not printed in the paper but is necessary, by the same example as for Theorem 4.12 ($q=0$, $r=1$, $N=[0]$, $M=[-1]$).
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, Corollary 4.13, p. 15, (4.9)

import Mathlib
import Definitions.Def_QuadMatIneq_Stabilization_QMI

open Matrix

namespace QuadMatIneq.Stabilization

/-- Corollary 4.13, p. 15. Inequality (4.9) is `M − αN ⩾ [βI 0; 0 0]`. The second statement
carries the added hypothesis `Nonempty ι` (`q ⩾ 1`), without which it fails
(`q = 0`, `r = 1`, `N = [0]`, `M = [−1]`). -/
theorem corollary_4_13 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hM : M.IsHermitian) (hN : N.IsHermitian) :
    ((∃ α β : ℝ, 0 ≤ α ∧ 0 < β ∧
        (M - α • N - Matrix.fromBlocks (β • (1 : Matrix ι ι ℝ)) 0 0 0).PosSemidef) →
      ZSet N ⊆ ZPlus M) ∧
    (Nonempty ι → InPi N → (-M.toBlocks₂₂).PosSemidef →
      (ZSet N ⊆ ZPlus M ↔
        ∃ α β : ℝ, 0 ≤ α ∧ 0 < β ∧
          (M - α • N - Matrix.fromBlocks (β • (1 : Matrix ι ι ℝ)) 0 0 0).PosSemidef)) := by sorry

end QuadMatIneq.Stabilization
