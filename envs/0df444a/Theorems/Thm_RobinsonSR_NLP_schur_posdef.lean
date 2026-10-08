-- Prove2me | Theorems.Thm_RobinsonSR_NLP_schur_posdef
-- name    : RobinsonSR.NLP.schur_posdef
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:12.493136+00:00
-- url     : https://prove2.me/theorems/6f08c43e-42b2-4ae2-beba-9c4ade86566e
-- title:
--   Proof of Theorem 4.1, p. 56 — under (a′) and (b) the Schur complement (4.6) is positive definite
-- statement:
--   Let $Q$ ($n\times n$, symmetric), $H$ ($q\times n$), $G^+$ ($r\times n$) and $G^0$ ($s\times n$) be real matrices. Assume
--   1. the strong second-order sufficient condition: $\langle y,Qy\rangle>0$ for every nonzero $y$ with $G^+y=0$ and $Hy=0$;
--   2. linear independence (b): the rows of $G^+$, $G^0$ and $H$ are jointly linearly independent, i.e. $H^Tb+G^{+T}c+G^{0T}d=0$ implies $b=0$, $c=0$, $d=0$.
--
--   Then the Schur complement
--   $$S=\begin{bmatrix}G^0&0&0\end{bmatrix}\begin{bmatrix}Q&H^{T}&G^{+T}\\-H&0&0\\-G^{+}&0&0\end{bmatrix}^{-1}\begin{bmatrix}G^{0T}\\0\\0\end{bmatrix}\qquad(4.6)$$
--   is positive definite: $\langle z,Sz\rangle>0$ for every $z\ne0$.
--
--   Together with the two previous steps this shows that $S$ is a P-matrix, the condition of the §4 criterion.
--
--   **Formalization Note** The nonsingularity of (4.5) is not assumed: it follows from the two hypotheses.
-- source:
--   Robinson, Strongly regular generalized equations, Math. Oper. Res. 5 (1980), p. 56, proof of Theorem 4.1, (4.6), (4.8)

import Mathlib
import Definitions.Def_RobinsonSR_NLP_Setting
open scoped RealInnerProductSpace Matrix

namespace RobinsonSR.NLP

/-- Proof of Theorem 4.1, p. 56: under the strong second-order sufficient condition, symmetry of
`ℒ″` and linear independence of the rows of `G⁺`, `G⁰` and `H`, the Schur complement (4.6) is
positive definite. -/
theorem schur_posdef {ιn ιq ιr ιs : Type*} [Fintype ιn] [Fintype ιq] [Fintype ιr]
    [Fintype ιs] [DecidableEq ιn] [DecidableEq ιq] [DecidableEq ιr]
    (Q : Matrix ιn ιn ℝ) (H : Matrix ιq ιn ℝ) (Gp : Matrix ιr ιn ℝ) (G0 : Matrix ιs ιn ℝ)
    (hQ : Q.IsSymm)
    (hSSOSC : ∀ y : ιn → ℝ, y ≠ 0 → Gp *ᵥ y = 0 → H *ᵥ y = 0 → 0 < y ⬝ᵥ (Q *ᵥ y))
    (hLI : ∀ (b : ιq → ℝ) (c : ιr → ℝ) (d : ιs → ℝ),
      Hᵀ *ᵥ b + Gpᵀ *ᵥ c + G0ᵀ *ᵥ d = 0 → b = 0 ∧ c = 0 ∧ d = 0) :
    RobinsonSR.Schur.PosDefNS (schurS Q H Gp G0) := by sorry

end RobinsonSR.NLP
