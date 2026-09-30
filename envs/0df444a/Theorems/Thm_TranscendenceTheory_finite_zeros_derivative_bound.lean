-- Prove2me | Theorems.Thm_TranscendenceTheory_finite_zeros_derivative_bound
-- name    : TranscendenceTheory.finite_zeros_derivative_bound
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T13:10:04.941394+00:00
-- url     : https://prove2.me/theorems/79c00eb4-cf16-41c4-8125-56b46b4b1bd3
-- title:
--   Schwarz decay and Cauchy derivative bounds from finitely many vanishing jets
-- statement:
--   Let $f:\mathbb C\to\mathbb C$ be entire, let $S$ be a finite set of complex numbers, and assign to each $a\in S$ a nonnegative integer $m_a$. Suppose
--
--   $$
--   f^{(j)}(a)=0\qquad(a\in S,\ 0\le j<m_a).
--   $$
--
--   Let $0<r<R$ and $C\in\mathbb R$. Assume $|a|\le r$ for every $a\in S$ and $|f(z)|\le C$ on the circle $|z|=R$. Put $N=\sum_{a\in S}m_a$. Then
--
--   $$
--   |f(z)|\le C\left(\frac{2r}{R}\right)^N\qquad(|z|\le r).
--   $$
--
--   Moreover, for every $w\in\mathbb C$, every $\rho>0$ with $|w|+\rho\le r$, and every nonnegative integer $n$,
--
--   $$
--   |f^{(n)}(w)|\le
--   \frac{n!}{\rho^n}\,C\left(\frac{2r}{R}\right)^N.
--   $$
--
--   Empty sets, zero assigned multiplicities, and the identically zero function are included. This is the finite vanishing-jet form of the analytic estimate used before Lemma 6 in the source. Taking $\rho=1$ recovers its derivative estimate; the statement also allows zeros on the inner boundary and arbitrary positive Cauchy radii.
-- source:
--   Senthil Kumar K (2026), Section 4, equations (14) and (15), immediately before Lemma 6. Supporting formulation using a finite set with prescribed zero multiplicities and an arbitrary positive Cauchy radius; the exact decay factor 2r/R is retained. https://doi.org/10.1017/S001309152610145X

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CanonicalDecomposition

open Filter Metric Set

theorem TranscendenceTheory.finite_zeros_derivative_bound (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f univ) (s : Finset ℂ) (m : ℂ → ℕ)
    (hm : ∀ a ∈ s, ∀ j < m a, iteratedDeriv j f a = 0)
    (r R C : ℝ) (hr : 0 < r) (hrR : r < R)
    (hs : ∀ a ∈ s, ‖a‖ ≤ r)
    (hC : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ C) :
    (∀ z : ℂ, ‖z‖ ≤ r → ‖f z‖ ≤ C * (2 * r / R) ^ (∑ a ∈ s, m a)) ∧
    ∀ (w : ℂ) (ρ : ℝ), 0 < ρ → ‖w‖ + ρ ≤ r → ∀ n : ℕ,
      ‖iteratedDeriv n f w‖ ≤
        n.factorial * (C * (2 * r / R) ^ (∑ a ∈ s, m a)) / ρ ^ n := by sorry
