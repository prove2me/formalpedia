-- Prove2me | Theorems.Thm_RobinsonSR_NLP_schur_eq_and_symm
-- name    : RobinsonSR.NLP.schur_eq_and_symm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:13.075601+00:00
-- url     : https://prove2.me/theorems/b27104c7-5a67-4769-bd3b-a221e5e894ed
-- title:
--   Proof of Theorem 4.1, p. 56 — (4.8) defines V uniquely, S = G⁰V = VᵀℒʺV, so S is symmetric
-- statement:
--   Let $Q$ ($n\times n$), $H$ ($q\times n$), $G^+$ ($r\times n$) and $G^0$ ($s\times n$) be real matrices, assume the matrix (4.5) built from $Q,H,G^+$ is nonsingular and $Q$ is symmetric, and let $S$ be the Schur complement (4.6). Then:
--   1. the equations
--   $$Q V+H^TA+G^{+T}B=G^{0T},\qquad -HV=0,\qquad -G^+V=0\qquad(4.8)$$
--   have exactly one solution $(V,A,B)$ with $V$ $n\times s$, $A$ $q\times s$, $B$ $r\times s$;
--   2. every solution of (4.8) satisfies
--   $$S=G^0V\qquad\text{and}\qquad S=V^TQV;$$
--   3. $S$ is symmetric.
--
--   In the proof of Theorem 4.1 this identifies the Schur complement with a quadratic form of $\mathcal L''$ restricted to the null space of $H$ and $G^+$.
-- source:
--   Robinson, Strongly regular generalized equations, Math. Oper. Res. 5 (1980), p. 56, proof of Theorem 4.1, (4.6), (4.8)

import Mathlib
import Definitions.Def_RobinsonSR_NLP_Setting
open scoped RealInnerProductSpace Matrix

namespace RobinsonSR.NLP

/-- Proof of Theorem 4.1, p. 56: if the matrix (4.5) is nonsingular, the equations (4.8)
`ℒ″V + HᵀA + G⁺ᵀB = G⁰ᵀ, −HV = 0, −G⁺V = 0` have exactly one solution `(V, A, B)`; for it the
Schur complement (4.6) satisfies `S = G⁰V`, and, `ℒ″` being symmetric, `S = VᵀℒʺV`; hence `S` is
symmetric. -/
theorem schur_eq_and_symm {ιn ιq ιr ιs : Type*} [Fintype ιn] [Fintype ιq] [Fintype ιr]
    [Fintype ιs] [DecidableEq ιn] [DecidableEq ιq] [DecidableEq ιr]
    (Q : Matrix ιn ιn ℝ) (H : Matrix ιq ιn ℝ) (Gp : Matrix ιr ιn ℝ) (G0 : Matrix ιs ιn ℝ)
    (hK : (kktMatrix Q H Gp).det ≠ 0) (hQ : Q.IsSymm) :
    (∃! VAB : Matrix ιn ιs ℝ × Matrix ιq ιs ℝ × Matrix ιr ιs ℝ,
        Q * VAB.1 + Hᵀ * VAB.2.1 + Gpᵀ * VAB.2.2 = G0ᵀ ∧ -H * VAB.1 = 0 ∧ -Gp * VAB.1 = 0) ∧
    (∀ (V : Matrix ιn ιs ℝ) (A : Matrix ιq ιs ℝ) (B : Matrix ιr ιs ℝ),
        Q * V + Hᵀ * A + Gpᵀ * B = G0ᵀ → -H * V = 0 → -Gp * V = 0 →
          schurS Q H Gp G0 = G0 * V ∧ schurS Q H Gp G0 = Vᵀ * Q * V) ∧
    (schurS Q H Gp G0).IsSymm := by sorry

end RobinsonSR.NLP
