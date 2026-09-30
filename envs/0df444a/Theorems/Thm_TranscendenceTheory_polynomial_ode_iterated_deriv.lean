-- Prove2me | Theorems.Thm_TranscendenceTheory_polynomial_ode_iterated_deriv
-- name    : TranscendenceTheory.polynomial_ode_iterated_deriv
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T11:18:36.801492+00:00
-- url     : https://prove2.me/theorems/f33f6490-4860-4162-8a4e-3ab61a20213f
-- title:
--   Iterated polynomial differentiation along a quadratic differential system
-- statement:
--   Let $I$ be a finite index set and let $D$ be a $\mathbb Z$-linear derivation of $\mathbb Z[X_i:i\in I]$ such that
--
--   $$
--   \deg(DX_i)\le 2\qquad(i\in I).
--   $$
--
--   Let $U\subseteq\mathbb C$ be open, and suppose $f_i:\mathbb C\to\mathbb C$ satisfies, at every $z\in U$,
--
--   $$
--   f_i'(z)=(DX_i)(f(z)).
--   $$
--
--   Here evaluation uses the canonical embedding of integer coefficients into $\mathbb C$, and existence of the displayed complex derivatives is part of the hypothesis. Then, for every integer polynomial $p$ and every $n\ge0$,
--
--   $$
--   \deg(D^np)\le\deg p+n,
--   \qquad
--   \frac{d^n}{dz^n}p(f(z))=(D^np)(f(z))\quad(z\in U).
--   $$
--
--   The total degree of the zero polynomial is taken to be zero. The statement includes constant polynomials, derivative order zero, an empty index set, and an empty open set. It gives the polynomial-presentation and degree step in the higher-derivative argument for Weierstrass elliptic and zeta functions; it makes no coefficient-height assertion.
-- source:
--   Senthil Kumar K (2026), Section 4, Lemma 4, polynomial differentiation step in equations (8)-(10), used after the cleared addition expansion (7). This is the general quadratic polynomial differential-system lemma underlying that step, including constant coordinates; it isolates exact presentations and degree growth, not the coefficient-height part of Lemma 4. https://doi.org/10.1017/S001309152610145X

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FinCases

noncomputable section

open MvPolynomial Filter
open scoped Topology

theorem TranscendenceTheory.polynomial_ode_iterated_deriv {σ : Type} [Fintype σ]
    (D : Derivation ℤ (MvPolynomial σ ℤ) (MvPolynomial σ ℤ))
    (hD : ∀ i, (D (X i)).totalDegree ≤ 2)
    (U : Set ℂ) (hU : IsOpen U) (f : σ → ℂ → ℂ)
    (hf : ∀ z ∈ U, ∀ i, HasDerivAt (f i)
      (eval₂ (Int.castRingHom ℂ) (fun i => f i z) (D (X i))) z)
    (p : MvPolynomial σ ℤ) (n : ℕ) :
    (D^[n] p).totalDegree ≤ p.totalDegree + n ∧
      ∀ z ∈ U, iteratedDeriv n
        (fun w => eval₂ (Int.castRingHom ℂ) (fun i => f i w) p) z =
          eval₂ (Int.castRingHom ℂ) (fun i => f i z) (D^[n] p) := by sorry
