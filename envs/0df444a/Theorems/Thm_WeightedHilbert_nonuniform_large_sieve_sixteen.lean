-- Prove2me | Theorems.Thm_WeightedHilbert_nonuniform_large_sieve_sixteen
-- name    : WeightedHilbert_nonuniform_large_sieve_sixteen
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-20T17:39:42.088088+00:00
-- url     : https://prove2.me/theorems/ee72dd79-89b1-4fab-8700-1074eec4cacc
-- title:
--   A nonuniform large sieve with individual frequency spacings
-- statement:
--   Let $N$ be a nonnegative integer, $(\theta_r)_{r\in I}$ a finite family of real frequencies, and $a_0,\ldots,a_{N-1}$ complex coefficients. For each frequency choose $0<\delta_r\le1$ such that
--   $$\delta_r\le |\theta_r-\theta_s+m|\qquad(r\ne s,\ m\in\mathbb Z).$$
--   Writing $e(t)=\exp(2\pi it)$, the nonuniform large-sieve estimate is
--   $$\sum_{r\in I}\frac{\left|\sum_{n=0}^{N-1}a_n e(n\theta_r)\right|^2}{N+16/\delta_r}
--   \le \sum_{n=0}^{N-1}|a_n|^2.$$
--   Each frequency retains its own separation scale. The constant 16 is explicit and nonsharp. In applications to reduced rational frequencies $a/q$ with $q\le z$, a bound $\delta_{a/q}\ge1/(qz)$ gives the conductor-dependent denominator $N+16qz$. Establishing that rational-spacing bound and the arithmetic lower-energy estimate are separate steps; this theorem does not assert a prime-pair counting bound.
--
--   Formalization Note: the index type may be empty or singleton, and $N=0$ is allowed. All denominators are strictly positive under the stated hypotheses. The coefficient sequence is arbitrary because only its first $N$ values occur.
-- source:
--   Finite Fourier and weighted-duality consequence of the accepted circle Hilbert estimate https://prove2.me/theorems/de62b18a-6cc5-46cb-9555-8b45ad09f4bf, itself derived from the Montgomery–Vaughan real Hilbert inequality via the accepted Zeta23 constant-13 development. This is a coarse constant-16 consequence, not a claim of a new mathematical large-sieve theorem or of the original sharp constant. Intended analytic input to the prime-pair route for https://prove2.me/theorems/0b3aa912-642f-4b13-b915-0b43c7e7c385.

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open scoped BigOperators

theorem WeightedHilbert_nonuniform_large_sieve_sixteen
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (θ δ : ι → ℝ) (a : ℕ → ℂ)
    (hpos : ∀ r, 0 < δ r) (hunit : ∀ r, δ r ≤ 1)
    (hgap : ∀ r s, r ≠ s → ∀ m : ℤ, δ r ≤ |θ r-θ s+m|) :
    (∑ r, ‖∑ n ∈ Finset.range N,
      a n * Complex.exp (2*(Real.pi : ℂ)*Complex.I*(n : ℂ)*(θ r : ℂ))‖^2 /
      ((N : ℝ)+16/δ r)) ≤ ∑ n ∈ Finset.range N, ‖a n‖^2 := by sorry
