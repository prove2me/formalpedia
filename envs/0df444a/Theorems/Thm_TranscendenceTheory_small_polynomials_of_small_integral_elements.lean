-- Prove2me | Theorems.Thm_TranscendenceTheory_small_polynomials_of_small_integral_elements
-- name    : TranscendenceTheory.small_polynomials_of_small_integral_elements
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-05T03:15:53.674709+00:00
-- url     : https://prove2.me/theorems/1b26877c-0fc6-45a7-ba2f-3ddd5d99c3d7
-- title:
--   Integer polynomials from small elements in a finite free algebra
-- statement:
--   Let θ be a complex number transcendental over Z. Let S be a commutative integral domain and a finite free algebra over Z[X], with basis b₀,…,b_d and b₀=1. Let φ:S→C be a ring homomorphism satisfying φ(p·1)=p(θ) for every integer polynomial p. Write qᵢ(x)∈Z[X] for the basis coordinates of x∈S.
--
--   Suppose C,c>0 and every sufficiently large integer N admits x_N≠0 such that
--   $$
--   \deg q_i(x_N)\le CN,\qquad |[X^k]q_i(x_N)|\le e^{CN},\qquad
--   |\varphi(x_N)|\le e^{-cN^2\log N}.
--   $$
--   Then there are A>0 and N₀ such that every integer N≥N₀ admits p_N∈Z[X] with
--   $$
--   \deg p_N\le AN,\qquad |[X^k]p_N|\le e^{AN},\qquad
--   0<|p_N(\theta)|\le e^{-10(AN)^2}.
--   $$
--   This statement isolates the norm-transfer step used to turn small integral elements into integer polynomials in a transcendental parameter. All bounds are uniform in N; the rank, basis, algebra, and homomorphism are fixed. Rank one is included.
--
--   **Formalization Note.** The input is eventual existence of elements, so no chosen sequence is required. The polynomial action and its compatibility with φ are explicit hypotheses.
-- source:
--   Determinant formulation of the norm-transfer argument in Senthil Kumar K (2026), Section 5, paragraphs immediately after Lemma 10, from the definition of theta_N through its degree and coefficient estimates; https://doi.org/10.1017/S001309152610145X. The finite free algebra form is a generalization of the fixed integral power-basis setting in Section 3. The degree envelope is relaxed to a linear one.

import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Polynomial Module Filter
open scoped Polynomial

namespace TranscendenceTheory

theorem small_polynomials_of_small_integral_elements
    {S : Type*} [CommRing S] [IsDomain S] [Algebra ℤ[X] S]
    (θ : ℂ) (hθ : Transcendental ℤ θ)
    (φ : S →+* ℂ)
    (hφ : ∀ p : ℤ[X], φ (algebraMap ℤ[X] S p) = aeval θ p)
    (d : ℕ) (b : Basis (Fin (d + 1)) ℤ[X] S) (hb : b 0 = 1)
    (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hsmall : ∀ᶠ N : ℕ in atTop, ∃ x : S, x ≠ 0 ∧
      (∀ i, ((b.repr x i).natDegree : ℝ) ≤ C * N) ∧
      (∀ i k, |((b.repr x i).coeff k : ℝ)| ≤ Real.exp (C * N)) ∧
      ‖φ x‖ ≤ Real.exp (-c * (N : ℝ) ^ 2 * Real.log N)) :
    ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ p : ℤ[X], (p.natDegree : ℝ) ≤ A * N ∧
        (∀ k, |(p.coeff k : ℝ)| ≤ Real.exp (A * N)) ∧
        0 < ‖aeval θ p‖ ∧ ‖aeval θ p‖ ≤ Real.exp (-10 * (A * N) ^ 2) := by sorry

end TranscendenceTheory
