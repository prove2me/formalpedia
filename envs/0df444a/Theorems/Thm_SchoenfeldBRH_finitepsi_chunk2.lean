-- Prove2me | Theorems.Thm_SchoenfeldBRH_finitepsi_chunk2
-- name    : SchoenfeldBRH.finitepsi_chunk2
-- status  : Proved
-- author  : @xuanji
-- created : 2026-11-24T03:07:53.870498+00:00
-- url     : https://prove2.me/theorems/11274790-09b7-4d5d-b47e-1b76897b2040
-- title:
--   Finite check of Schoenfeld's psi bound on [214499, 330047)
-- statement:
--   Explicit finite verification of the Schoenfeld-type bound for Chebyshev's function on a window.
--
--   Let $\psi(x)=\sum_{n\le x}\Lambda(n)$ and $W=2^{20}$. Assume the certified enclosure $\frac{324600561728}{W}\log 2 \le \psi(214499) \le \frac{324603956688}{W}\log 2$. Then
--
--   $$|\psi(x)-x| < \frac{\sqrt{x}\,\log^2 x}{8\pi} \qquad (214499\le x<330047),$$
--
--   and moreover $\frac{499553927232}{W}\log 2 \le \psi(330047) \le \frac{499559583184}{W}\log 2$. This is chunk 2 of a kernel-checked computation of $\psi$ (via $\psi(B)-\psi(A)=\log\prod_{A<m\le B} e^{\Lambda(m)}$ and bit-length bounds) proving Schoenfeld's bound on $[73.2, e^{13}]$; the enclosures chain the chunks together.
-- source:
--   Schoenfeld 1976, Sharper bounds for the Chebyshev functions theta(x) and psi(x) II, Math. Comp. 30, Theorem 10 (finite range part)

import Mathlib

theorem SchoenfeldBRH.finitepsi_chunk2 :
    ((324600561728 : ℝ) / 1048576 * Real.log 2 ≤ Chebyshev.psi (214499 : ℝ) ∧
      Chebyshev.psi (214499 : ℝ) ≤ (324603956688 : ℝ) / 1048576 * Real.log 2) →
    (∀ x : ℝ, (214499 : ℝ) ≤ x → x < (330047 : ℝ) →
      |Chebyshev.psi x - x| < Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi)) ∧
    ((499553927232 : ℝ) / 1048576 * Real.log 2 ≤ Chebyshev.psi (330047 : ℝ) ∧
      Chebyshev.psi (330047 : ℝ) ≤ (499559583184 : ℝ) / 1048576 * Real.log 2) := by sorry
