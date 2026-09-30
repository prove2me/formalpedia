-- Prove2me | Theorems.Thm_TranscendenceTheory_exists_integral_generator_and_common_denominator
-- name    : TranscendenceTheory.exists_integral_generator_and_common_denominator
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-05T11:22:13.906872+00:00
-- url     : https://prove2.me/theorems/24f1677c-9d54-45b3-a685-3ed7a736c873
-- title:
--   An integral generator and a common polynomial denominator
-- statement:
--   Let $\theta\in\mathbb C$ be transcendental over $\mathbb Q$, and let $(v_i)_{i\in I}$ be a finite family of complex numbers algebraic over $\mathbb Q(\theta)$. There exist a complex number $\nu$ integral over $\mathbb Z[\theta]$, a polynomial $d\in\mathbb Z[X]$ with $d(\theta)\ne0$, and polynomials $p_i\in\mathbb Z[X,Y]$ such that
--
--   $$
--   p_i(\theta,\nu)=d(\theta)v_i\qquad(i\in I).
--   $$
--
--   Integrality is witnessed by a monic polynomial in $Y$ with coefficients in $\mathbb Z[X]$ vanishing at $(\theta,\nu)$. All values share the same generator and denominator. The family may be empty or contain zero, and the original values need not be integral. This supplies a fixed polynomial model for finite algebraic data over a field of transcendence degree one.
--
--   **Formalization Note.** Algebraicity is stated over $\mathbb Q[\theta]$, equivalently over its fraction field. Bivariate polynomials are represented as $\mathbb Z[X][Y]$.
-- source:
--   Senthil Kumar K (2026), Section 3, integral-generator setup and denominator representation preceding Lemma 1; https://doi.org/10.1017/S001309152610145X. General finite-family formulation. Primitive element theorem: Stacks Project, Tag 030N, https://stacks.math.columbia.edu/tag/030N; Mathlib Field.exists_primitive_element, pinned commit 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Algebraic.Basic

open Polynomial

theorem TranscendenceTheory.exists_integral_generator_and_common_denominator {ι : Type*} [Fintype ι]
    (θ : ℂ) (hθ : Transcendental ℚ θ) (v : ι → ℂ)
    (hv : ∀ i, IsAlgebraic (Algebra.adjoin ℚ {θ}) (v i)) :
    ∃ ν : ℂ,
      (∃ f : ℤ[X][X], f.Monic ∧ f.eval₂ (aeval θ).toRingHom ν = 0) ∧
      ∃ d : ℤ[X], aeval θ d ≠ 0 ∧
        ∀ i, ∃ p : ℤ[X][X], p.eval₂ (aeval θ).toRingHom ν = aeval θ d * v i := by sorry
