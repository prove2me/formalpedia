-- Prove2me | Theorems.Thm_QAOAE3Lin2_General_eq_41
-- name    : QAOAE3Lin2.General.eq_41
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:33.586994+00:00
-- url     : https://prove2.me/theorems/b55f2a85-0a5b-45f8-8ef5-34063c88cef9
-- title:
--   Section II, (40)–(41), p. 8 — max_r |(m/2)γ_r + P^k(γ_r)| ≥ m/(20D^{1/2}k), γ_r = cos(πr/k)/(10D^{1/2})
-- statement:
--   Let a Max E3LIN2 instance with $m$ equations be given, let $D\ge1$, let $k$ be odd, and let
--   $$\gamma_r=\frac1{10D^{1/2}}\cos(\pi r/k),\qquad r=0,1,\dots,k .$$
--   Then
--   $$\max_{r=0,1,\dots,k}\Big|\frac m2\gamma_r+P^k(\gamma_r)\Big|\ge\frac m{20D^{1/2}k},$$
--   where $P^k$ is the sum of the $m$ polynomials (27).
--
--   This is the Chebyshev-node bound (39) applied to the main term of (37), on a grid of $k+1$ angles in $[-1/(10D^{1/2}),1/(10D^{1/2})]$.
--
--   **Formalization Note.** The maximum is stated as the existence of a grid index $r$. $D\ge1$ is added so that $D^{1/2}\neq0$. No condition on the triples is needed: $P^k$ is a polynomial in $\gamma$ with only odd powers $3,\dots,k$ for every instance.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm Applied to a Bounded Occurrence Constraint Problem, arXiv:1412.6062v2, p. 8, Section II, (40)–(41)

import Mathlib
import Definitions.Def_QAOAE3Lin2_General_Setting

namespace QAOAE3Lin2.General

theorem eq_41 {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool) (D : ℕ)
    (hD : 1 ≤ D) (k : ℕ) (hk : Odd k) :
    ∃ r ∈ Finset.range (k + 1), (m : ℝ) / (20 * Real.sqrt D * k) ≤
      |(m : ℝ) / 2 * gammaGrid D k r + PkSum tri rhs k (gammaGrid D k r)| := by sorry

end QAOAE3Lin2.General
