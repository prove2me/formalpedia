-- Prove2me | Theorems.Thm_RobinsonSR_NLP_matrix_4_5_nonsingular
-- name    : RobinsonSR.NLP.matrix_4_5_nonsingular
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:20.51858+00:00
-- url     : https://prove2.me/theorems/c4ed1697-c0b3-45c1-8416-ed03f512027c
-- title:
--   Proof of Theorem 4.1, p. 56 — the KKT matrix (4.5) is nonsingular
-- statement:
--   Let $Q$ be an $n\times n$, $H$ a $q\times n$ and $G^+$ an $r\times n$ real matrix (playing $\mathcal L''$, $h'(x_0)$ and $g^{+\prime}(x_0)$). Assume
--   1. the strong second-order sufficient condition: $\langle y,Qy\rangle>0$ for every nonzero $y$ with $G^+y=0$ and $Hy=0$;
--   2. the rows of $H$ and $G^+$ are jointly linearly independent: $H^Tb+G^{+T}c=0$ implies $b=0$ and $c=0$.
--
--   Then the matrix
--   $$\begin{bmatrix}Q&H^{T}&G^{+T}\\-H&0&0\\-G^{+}&0&0\end{bmatrix}\qquad(4.5)$$
--   is nonsingular.
--
--   This is the first step of the proof of Theorem 4.1: it makes the Schur complement (4.6) well defined.
--
--   **Formalization Note** The index sets are arbitrary finite types, so the statement covers the degenerate cases $n=0$, $q=0$ or $r=0$. The page applies the full linear independence assumption (b), which also involves $G^0$; only its consequence for $H$ and $G^+$ is used, and that is what is assumed here. $Q$ need not be symmetric.
-- source:
--   Robinson, Strongly regular generalized equations, Math. Oper. Res. 5 (1980), p. 56, proof of Theorem 4.1, (4.5), (4.7)

import Mathlib
import Definitions.Def_RobinsonSR_NLP_Setting
open scoped RealInnerProductSpace Matrix

namespace RobinsonSR.NLP

/-- Proof of Theorem 4.1, p. 56: under the strong second-order sufficient condition (on the null
space of `H` and `G⁺`) and linear independence of the rows of `H` and `G⁺`, the matrix (4.5)
`[ℒ″ Hᵀ G⁺ᵀ; −H 0 0; −G⁺ 0 0]` is nonsingular. -/
theorem matrix_4_5_nonsingular {ιn ιq ιr : Type*} [Fintype ιn] [Fintype ιq] [Fintype ιr]
    [DecidableEq ιn] [DecidableEq ιq] [DecidableEq ιr]
    (Q : Matrix ιn ιn ℝ) (H : Matrix ιq ιn ℝ) (Gp : Matrix ιr ιn ℝ)
    (hSSOSC : ∀ y : ιn → ℝ, y ≠ 0 → Gp *ᵥ y = 0 → H *ᵥ y = 0 → 0 < y ⬝ᵥ (Q *ᵥ y))
    (hLI : ∀ (b : ιq → ℝ) (c : ιr → ℝ), Hᵀ *ᵥ b + Gpᵀ *ᵥ c = 0 → b = 0 ∧ c = 0) :
    (kktMatrix Q H Gp).det ≠ 0 := by sorry

end RobinsonSR.NLP
