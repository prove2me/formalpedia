-- Prove2me | Theorems.Thm_TranscendenceTheory_quadratic_pair_power_recurrence
-- name    : TranscendenceTheory.quadratic_pair_power_recurrence
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-14T20:45:34.490212+00:00
-- url     : https://prove2.me/theorems/3dee585e-0934-413a-93ec-cd5c26b3f2c0
-- title:
--   Quadratic-pair power recurrence and norm identity
-- statement:
--   Let R be a commutative ring and let d,a,b,y∈R satisfy y²=d. Define pairs (uₙ,vₙ) by
--
--   $$u_0=1,\quad v_0=0,\qquad
--   u_{n+1}=a u_n+d b v_n,\quad v_{n+1}=b u_n+a v_n.$$
--
--   For every natural number n, including zero,
--
--   $$(a+yb)^n=u_n+yv_n,\qquad
--   u_n^2-dv_n^2=(a^2-db^2)^n.$$
--
--   The two coefficients are computed using only a,b,d. The identities require no division, no characteristic assumption, and no nonvanishing assumption on y. They remain valid over rings with zero divisors.
-- source:
--   Derived quadratic-pair recurrence step for https://prove2.me/theorems/331d9140-bf3f-4a7e-98d5-ccf5729c2b74. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. This is an algebraic tool for the interpolation frontier; the geometric zero estimate remains open. Primary Lean sources: Mathlib Algebra/QuadraticAlgebra/Defs.lean and Basic.lean, especially the universal lift and multiplicative norm, revision 0df444a360eaa60ab8c11dca51a86af692955474. The recurrence is multiplication in the quadratic algebra with generator squared equal to d. Its evaluation homomorphism reconstructs powers, and its multiplicative norm proves the norm identity. The frontier uses both identities with d equal to the Weierstrass cubic evaluated at the formal wp series. Both directions preserve all witnesses, weights and numerical bounds.

import Mathlib.Algebra.QuadraticAlgebra.Basic

theorem TranscendenceTheory.quadratic_pair_power_recurrence
    (R : Type*) [CommRing R] (d a b y : R) (hy : y ^ 2 = d) :
    let T : ℕ → R × R := Nat.rec (1, 0)
      (fun _ t => (a * t.1 + d * b * t.2, b * t.1 + a * t.2))
    ∀ n : ℕ,
      (a + y * b) ^ n = (T n).1 + y * (T n).2 ∧
        (T n).1 ^ 2 - d * (T n).2 ^ 2 = (a ^ 2 - d * b ^ 2) ^ n := by sorry
