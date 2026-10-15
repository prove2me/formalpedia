-- Prove2me | Theorems.Thm_QAOAE3Lin2_General_eq_37
-- name    : QAOAE3Lin2.General.eq_37
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:34.219264+00:00
-- url     : https://prove2.me/theorems/763cc184-b2d1-4f15-976c-72cb68525710
-- title:
--   Section II, (35)–(37), pp. 7–8 — |⟨−γ,π/4|C|−γ,π/4⟩| ≥ |(m/2)γ + P^k(γ)| − m(9D^{1/2}|γ|)^{k+2}
-- statement:
--   Let an instance of Max E3LIN2 with $m$ equations have every equation on three distinct bits, no triple carrying two equations, and every bit in at most $D+1$ equations, with $D\ge1$. Let $k$ be odd and $\gamma$ real. Then
--   $$\big|\langle-\gamma,\tfrac\pi4|C|-\gamma,\tfrac\pi4\rangle\big|\ge\Big|\frac m2\gamma+P^k(\gamma)\Big|-m\big(9D^{1/2}|\gamma|\big)^{k+2},$$
--   where $C=\tfrac12\sum d_{abc}Z_aZ_bZ_c$ and $P^k$ is the sum of the $m$ polynomials (27).
--
--   This separates the quantity (7) into a polynomial main term and an error controlled by (34).
--
--   **Formalization Note.** $\langle-\gamma,\tfrac\pi4|C|-\gamma,\tfrac\pi4\rangle$ is written as the expected satisfied count at $-\gamma$ minus $m/2$. $D\ge1$ is inherited from (34).
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm Applied to a Bounded Occurrence Constraint Problem, arXiv:1412.6062v2, pp. 7–8, Section II, (35)–(37)

import Mathlib
import Definitions.Def_QAOAE3Lin2_General_Setting

namespace QAOAE3Lin2.General

theorem eq_37 {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool) (D : ℕ)
    (htri : IsTripleFamily tri) (hocc : BoundedOccurrence tri D) (hD : 1 ≤ D)
    (k : ℕ) (hk : Odd k) (γ : ℝ) :
    |(m : ℝ) / 2 * γ + PkSum tri rhs k γ| - (m : ℝ) * (9 * Real.sqrt D * |γ|) ^ (k + 2) ≤
      |expSat tri rhs (-γ) (Real.pi / 4) - (m : ℝ) / 2| := by sorry

end QAOAE3Lin2.General
