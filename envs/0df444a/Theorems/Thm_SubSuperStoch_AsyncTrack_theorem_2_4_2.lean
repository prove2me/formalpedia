-- Prove2me | Theorems.Thm_SubSuperStoch_AsyncTrack_theorem_2_4_2
-- name    : SubSuperStoch.AsyncTrack.theorem_2_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:43:45.61788+00:00
-- url     : https://prove2.me/theorems/d7b631c6-76d4-4e60-a39d-81711a772bbf
-- title:
--   Theorem 2.4 2), p. 7 — positive diagonals and a deficient row feeding every row give ‖∏F_s‖_∞ < 1 and ρ(∏F_s) < 1
-- statement:
--   Let $F_1,F_2,\dots,F_q\in\mathbb R^{n\times n}$ be sub-stochastic matrices. Assume that
--
--   1. every diagonal entry of every $F_s$ is positive, $[F_s]_{ii}>0$ for $s=1,\dots,q$ and $i=1,\dots,n$;
--   2. for every row $i_2$ there are a row $i_1$ and indices $1\le s_1<s_2\le q$ such that
--   $$\Lambda_{i_1}[F_{s_1}]<1\qquad\text{and}\qquad [F_{s_2}]_{i_2i_1}>0 .$$
--
--   Then
--   $$\Big\|\prod_{s=1}^q F_s\Big\|_\infty<1\qquad\text{and}\qquad \rho\Big(\prod_{s=1}^q F_s\Big)<1,$$
--   where $\prod_{s=1}^q F_s=F_q\cdots F_1$, $\|\cdot\|_\infty$ is the largest absolute row sum and $\rho$ is the spectral radius over the complex eigenvalues.
--
--   A row whose sum is below one in an early factor passes its deficit, through a positive entry of a later factor, to the row it feeds; positive diagonals keep the deficit alive in the remaining factors. This is the tool by which the paper shows that products of the marginally stable matrices $M(k)$ over long enough windows are contractions (Lemma 3.2).
--
--   **Formalization Note** The page writes the second hypothesis as "there exist $1\le s_1<s_2\le q$ such that $\Lambda_{i_1}[F_{s_1}]<1$ and $[F_{s_2}]_{i_2i_1}>0$ for any $i_1,i_2$". Read literally, with one pair $s_1,s_2$ for all $i_1,i_2$, it would force every row of $F_{s_1}$ below one and $F_{s_2}$ to be entrywise positive. The proof fixes, for each $i_2$, one $i_1$ (and $s_1,s_2$), and the example on p. 8 uses different $s_2$ for different rows; the statement here follows that reading, $\forall i_2\,\exists i_1, s_1, s_2$. It is implied by the literal reading, so this theorem is at least as strong as the printed one. "Contain positive diagonal elements" is read as "all diagonal entries are positive", as the proof's use of $[\prod_{s=s_1+1}^{s_2-1}F_s]_{i_1i_1}>0$ requires. $\rho(\cdot)<1$ is stated as: every complex eigenvalue has modulus $<1$.
-- source:
--   Shi, Zheng, Shao, Cheng, arXiv:2004.01867v2, p. 7, Theorem 2.4 2) (proof pp. 7–8; example p. 8)

import Mathlib
import Definitions.Def_SubSuperStoch_AsyncTrack_Matrix

namespace SubSuperStoch.AsyncTrack

/-- Theorem 2.4 2) (p. 7): let `F₁, …, F_q` be sub-stochastic with positive diagonal entries, and
suppose that for every row `i₂` there are a row `i₁` and indices `1 ≤ s₁ < s₂ ≤ q` with
`Λ_{i₁}[F_{s₁}] < 1` and `[F_{s₂}]_{i₂ i₁} > 0`. Then `‖∏_{s=1}^q F_s‖_∞ < 1` and
`ρ(∏_{s=1}^q F_s) < 1` (every complex eigenvalue has modulus `< 1`). -/
theorem theorem_2_4_2 {n : ℕ} (F : ℕ → Matrix (Fin n) (Fin n) ℝ) (q : ℕ)
    (hF : ∀ s, 1 ≤ s → s ≤ q → IsSubStochastic (F s))
    (hdiag : ∀ s, 1 ≤ s → s ≤ q → ∀ i, 0 < F s i i)
    (hfeed : ∀ i₂, ∃ i₁ s₁ s₂, 1 ≤ s₁ ∧ s₁ < s₂ ∧ s₂ ≤ q ∧
      rowSum (F s₁) i₁ < 1 ∧ 0 < F s₂ i₂ i₁) :
    normInf (prodFrom F 1 q) < 1 ∧ ∀ μ ∈ specC (prodFrom F 1 q), ‖μ‖ < 1 := by sorry

end SubSuperStoch.AsyncTrack
