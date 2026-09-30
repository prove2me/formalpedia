-- Prove2me | Theorems.Thm_TranscendenceTheory_small_integral_coordinates_of_bivariate_values
-- name    : TranscendenceTheory.small_integral_coordinates_of_bivariate_values
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-05T04:03:39.376812+00:00
-- url     : https://prove2.me/theorems/f686167e-e0f2-49e9-aeec-2f4918dcb640
-- title:
--   Integral basis coordinates from small bivariate polynomial values
-- statement:
--   Let θ,ν be complex numbers. Assume θ is transcendental over Z and ν is integral over Z[θ]: there is a polynomial f(X,Y) with integer coefficients, monic as a polynomial in Y, such that f(θ,ν)=0. Fix A,c>0. Suppose that every sufficiently large nonnegative integer N admits P_N∈Z[X,Y] satisfying
--   $$
--   \deg_X P_N,\deg_Y P_N\le AN,\qquad
--   |[X^kY^j]P_N|\le e^{AN},\qquad
--   0<|P_N(\theta,\nu)|\le e^{-cN^2\log N}.
--   $$
--   Then there is a subring S of C containing θ, a finite basis b₀,…,b_d of S as a Z[X]-module with X acting as θ and b₀=1, and constants C,c'>0 such that every sufficiently large N admits a nonzero x_N∈S with
--   $$
--   \deg q_i(x_N)\le CN,\qquad |[X^k]q_i(x_N)|\le e^{CN},\qquad
--   |x_N|\le e^{-c'N^2\log N},
--   $$
--   where q_i(x_N)∈Z[X] are its basis coordinates. The ring and basis are independent of N.
--
--   This transfers degree and height bounds from arbitrary bivariate expressions to a fixed integral basis. The Y-degree may grow with N; the hypothesis does not require the polynomials to be reduced modulo an integral relation. Rank one and zero coordinates are included.
--
--   **Formalization Note.** Bivariate polynomials are represented as polynomials in Y with coefficients in Z[X]. The monic relation is stated by an existential witness, so the statement does not rely on a chosen algebra structure on C.
-- source:
--   Quantitative power-basis consequence of Senthil Kumar K (2026), Section 3, the polynomial coordinate representation preceding Lemma 1, Lemma 1(iii), and its proof by reducing powers of nu; https://doi.org/10.1017/S001309152610145X. This is the n=2 specialization with inputs theta and nu, with degree and coefficient-length bounds used in place of the paper's type. The fixed integral power basis is justified by the minimal polynomial over the integrally closed ring Z[X].

import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Polynomial Module Filter
open scoped Polynomial

namespace TranscendenceTheory

theorem small_integral_coordinates_of_bivariate_values
    (θ ν : ℂ) (hθ : Transcendental ℤ θ)
    (hν : ∃ f : ℤ[X][X], f.Monic ∧ f.eval₂ (aeval θ).toRingHom ν = 0)
    (A c : ℝ) (hA : 0 < A) (hc : 0 < c)
    (hsmall : ∀ᶠ N : ℕ in atTop, ∃ P : ℤ[X][X],
      (P.natDegree : ℝ) ≤ A * N ∧
      (∀ j, ((P.coeff j).natDegree : ℝ) ≤ A * N) ∧
      (∀ j k, |((P.coeff j).coeff k : ℝ)| ≤ Real.exp (A * N)) ∧
      P.eval₂ (aeval θ).toRingHom ν ≠ 0 ∧
      ‖P.eval₂ (aeval θ).toRingHom ν‖ ≤ Real.exp (-c * (N : ℝ) ^ 2 * Real.log N)) :
    ∃ (S : Subring ℂ) (hθS : θ ∈ S) (d : ℕ),
      letI : Algebra ℤ[X] S := (aeval (⟨θ, hθS⟩ : S)).toAlgebra
      ∃ b : Basis (Fin (d + 1)) ℤ[X] S, b 0 = 1 ∧
        ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
          ∀ᶠ N : ℕ in atTop, ∃ x : S, x ≠ 0 ∧
            (∀ i, ((b.repr x i).natDegree : ℝ) ≤ C * N) ∧
            (∀ i k, |((b.repr x i).coeff k : ℝ)| ≤ Real.exp (C * N)) ∧
            ‖(x : ℂ)‖ ≤ Real.exp (-c * (N : ℝ) ^ 2 * Real.log N) := by sorry

end TranscendenceTheory
