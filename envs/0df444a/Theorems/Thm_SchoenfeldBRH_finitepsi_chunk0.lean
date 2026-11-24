-- Prove2me | Theorems.Thm_SchoenfeldBRH_finitepsi_chunk0
-- name    : SchoenfeldBRH.finitepsi_chunk0
-- status  : Proved
-- author  : @xuanji
-- created : 2026-11-24T03:07:52.492058+00:00
-- url     : https://prove2.me/theorems/6bd60201-33aa-493b-a2b9-f9e6d588e356
-- title:
--   Finite check of Schoenfeld's psi bound on [73.2, 101113)
-- statement:
--   Explicit finite verification of the Schoenfeld-type bound for Chebyshev's function on a window.
--
--   Let $\psi(x)=\sum_{n\le x}\Lambda(n)$ and $W=2^{20}$. Then
--
--   $$|\psi(x)-x| < \frac{\sqrt{x}\,\log^2 x}{8\pi} \qquad (73.2\le x<101113),$$
--
--   and moreover $\frac{152949030976}{W}\log 2 \le \psi(101113) \le \frac{152950689232}{W}\log 2$. This is chunk 0 of a kernel-checked computation of $\psi$ (via $\psi(B)-\psi(A)=\log\prod_{A<m\le B} e^{\Lambda(m)}$ and bit-length bounds) proving Schoenfeld's bound on $[73.2, e^{13}]$; the enclosures chain the chunks together.
-- source:
--   Schoenfeld 1976, Sharper bounds for the Chebyshev functions theta(x) and psi(x) II, Math. Comp. 30, Theorem 10 (finite range part)

import Mathlib

theorem SchoenfeldBRH.finitepsi_chunk0 :
    (∀ x : ℝ, (73.2 : ℝ) ≤ x → x < (101113 : ℝ) →
      |Chebyshev.psi x - x| < Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi)) ∧
    ((152949030976 : ℝ) / 1048576 * Real.log 2 ≤ Chebyshev.psi (101113 : ℝ) ∧
      Chebyshev.psi (101113 : ℝ) ≤ (152950689232 : ℝ) / 1048576 * Real.log 2) := by sorry
