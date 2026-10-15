-- Prove2me | Theorems.Thm_QAOAE3Lin2_General_eq_44_45
-- name    : QAOAE3Lin2.General.eq_44_45
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:21.669569+00:00
-- url     : https://prove2.me/theorems/28658437-eb17-4d46-9976-706ce0d703dc
-- title:
--   Section II, (44)–(45), pp. 8–9 — for large D, on every instance with occurrence ≤ D + 1, some γ_r of an odd k ≈ 5 ln D grid gives expected satisfied count ≥ (1/2 + 1/(101D^{1/2} ln D))m
-- statement:
--   There is a threshold $D_0$ such that for every natural number $D\ge D_0$ there is an odd integer $k$ with $5\ln D\le k\le5\ln D+2$ with the following property. For **every** instance of Max E3LIN2, with any number $n$ of bits and $m$ of equations, in which every equation is on three distinct bits, no triple carries two equations, and every bit lies in at most $D+1$ equations, there is an $r\in\{0,1,\dots,k\}$ such that the level-one QAOA state $|\gamma_r,\pi/4\rangle$ with
--   $$\gamma_r=\frac1{10D^{1/2}}\cos(\pi r/k)$$
--   has expected number of satisfied equations, when measured in the computational basis,
--   $$\sum_x|\langle x|\gamma_r,\tfrac\pi4\rangle|^2C(x)\;\ge\;\Big(\frac12+\frac1{101D^{1/2}\ln D}\Big)m .$$
--
--   This is the paper's main result: the level-one QAOA beats the random assignment's $m/2$ by $\Omega(m/(D^{1/2}\ln D))$ on every bounded-occurrence instance, using only $O(\ln D)$ angles. Equivalently (44): $\max_r\langle\gamma_r,\pi/4|C|\gamma_r,\pi/4\rangle\ge m/(101D^{1/2}\ln D)$ with $C=\tfrac12\sum d_{abc}Z_aZ_bZ_c$.
--
--   **Formalization Note.** "For large $D$" is the existential threshold $D_0$, and $D_0$ and $k$ depend on $D$ only, not on the instance. The page's "$k=5\ln D$" is pinned as an odd $k$ in $[5\ln D,5\ln D+2]$, since the argument needs $k$ odd; the grid then has $k+1\le5\ln D+3$ angles rather than the page's "no more than $5\ln D$". The statement is (45) in expectation, i.e. (44) shifted by $m/2$. The sampling claim that follows (45) on p. 9 is not part of this statement.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm Applied to a Bounded Occurrence Constraint Problem, arXiv:1412.6062v2, pp. 8–9, Section II, (44)–(45) (also abstract, p. 1)

import Mathlib
import Definitions.Def_QAOAE3Lin2_General_Setting

namespace QAOAE3Lin2.General

theorem eq_44_45 :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → ∃ k : ℕ, Odd k ∧ 5 * Real.log D ≤ k ∧
      (k : ℝ) ≤ 5 * Real.log D + 2 ∧
      ∀ (n m : ℕ) (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool),
        IsTripleFamily tri → BoundedOccurrence tri D →
        ∃ r ∈ Finset.range (k + 1),
          (1 / 2 + 1 / (101 * Real.sqrt D * Real.log D)) * (m : ℝ) ≤
            expSat tri rhs (gammaGrid D k r) (Real.pi / 4) := by sorry

end QAOAE3Lin2.General
