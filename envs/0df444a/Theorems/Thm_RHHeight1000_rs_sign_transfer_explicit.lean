-- Prove2me | Theorems.Thm_RHHeight1000_rs_sign_transfer_explicit
-- name    : RHHeight1000.rs_sign_transfer_explicit
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-19T17:03:51.431457+00:00
-- url     : https://prove2.me/theorems/03a3ef4a-0c04-4307-a258-97193d2bffd6
-- title:
--   Explicit Riemann–Siegel sign certificates bracket a critical-line zero
-- statement:
--   Let $A(t)$ be the Riemann–Siegel approximant with the second-order Stirling phase and the constant and linear correction terms, given explicitly in the formal statement, and put $$E(t)=\frac{25}{4}\left(\frac{t}{2\pi}\right)^{-5/4}+\frac{1}{32}\left(\frac{t}{2\pi}\right)^{-15/4}.$$ If $32\pi\le a\le b$, $A(a)A(b)<0$, and $E(a)<|A(a)|$, $E(b)<|A(b)|$, then $$\exists t\in(a,b):\ \zeta(\tfrac12+it)=0.$$ This is the analytic transfer lemma for the Riemann–Siegel interval certificates in the finite-height project.
-- source:
--   Salvatore Mercuri and Bhavik Mehta, smmercuri/zeta, commit 3dab6480a82f1bfc5de0a59550e279cf50490033, Apache-2.0. Adapted by source dependency pruning from riemannZeta.exists_zero_of_zIntervalRS_certificate. Original authorship notices preserved.

import Mathlib
open scoped Real BigOperators
open MeasureTheory

theorem RHHeight1000.rs_sign_transfer_explicit :
 let A : ℝ → ℝ := fun (t : ℝ) =>
  (fun (θ t : ℝ) (ν : ℕ) => 2 * ∑ n ∈ Finset.Icc 1 ν, Real.cos (θ - t * Real.log ↑n) / √↑n)
      ((fun (M N : ℕ) (t : ℝ) =>
          ((fun (M : ℕ) (w : ℂ) =>
                    (w - 1 / 2) * Complex.log w - w + 1 / 2 * ↑(Real.log (2 * Real.pi)) +
                      ∑ k ∈ Finset.Icc 1 M, ↑(bernoulli (2 * k)) / (2 * ↑k * (2 * ↑k - 1)) * w ^ (1 - 2 * (k : ℤ)))
                  M (1 / 4 + Complex.I * (↑t / 2) + ↑N) -
                ∑ j ∈ Finset.range N, Complex.log (1 / 4 + Complex.I * (↑t / 2) + ↑j)).im -
            t / 2 * Real.log Real.pi)
        2 0 t)
      t ⌊√(t / (2 * Real.pi))⌋₊ -
    (-1) ^ ⌊√(t / (2 * Real.pi))⌋₊ * (t / (2 * Real.pi)) ^ (-(1 / 4) : ℝ) *
      ((fun (p : ℝ) =>
            2 *
              (Complex.exp (-(↑(Real.pi / 8) * Complex.I)) *
                  (fun (p : ℂ) (a : ℝ) =>
                      (1 + Complex.I) *
                        ∫ (w : ℝ),
                          (fun (p : ℂ) (a w : ℝ) =>
                              (fun (p x : ℂ) =>
                                  Complex.exp (2 * ↑Real.pi * Complex.I * (x - p) ^ 2) /
                                    (Complex.exp (↑Real.pi * Complex.I * x) -
                                      Complex.exp (-(↑Real.pi * Complex.I * x))))
                                p ((fun (a w : ℝ) => ↑(a + w) + ↑w * Complex.I) a w))
                            p a w)
                    (↑p) (1 / 2)).re)
          (√(t / (2 * Real.pi)) - ↑⌊√(t / (2 * Real.pi))⌋₊) +
        (fun (p : ℝ) =>
              2 *
                (Complex.exp (-(↑(Real.pi / 8) * Complex.I)) *
                    (-(1 / 2) *
                        (fun (n : ℕ) (p : ℂ) (a : ℝ) =>
                            (1 + Complex.I) *
                              ∫ (w : ℝ),
                                (fun (n : ℕ) (p : ℂ) (a w : ℝ) =>
                                    ((fun (a w : ℝ) => ↑(a + w) + ↑w * Complex.I) a w - p) ^ n *
                                      (fun (p : ℂ) (a w : ℝ) =>
                                          (fun (p x : ℂ) =>
                                              Complex.exp (2 * ↑Real.pi * Complex.I * (x - p) ^ 2) /
                                                (Complex.exp (↑Real.pi * Complex.I * x) -
                                                  Complex.exp (-(↑Real.pi * Complex.I * x))))
                                            p ((fun (a w : ℝ) => ↑(a + w) + ↑w * Complex.I) a w))
                                        p a w)
                                  n p a w)
                          1 (↑p) (1 / 2) -
                      2 * ↑Real.pi * Complex.I / 3 *
                        (fun (n : ℕ) (p : ℂ) (a : ℝ) =>
                            (1 + Complex.I) *
                              ∫ (w : ℝ),
                                (fun (n : ℕ) (p : ℂ) (a w : ℝ) =>
                                    ((fun (a w : ℝ) => ↑(a + w) + ↑w * Complex.I) a w - p) ^ n *
                                      (fun (p : ℂ) (a w : ℝ) =>
                                          (fun (p x : ℂ) =>
                                              Complex.exp (2 * ↑Real.pi * Complex.I * (x - p) ^ 2) /
                                                (Complex.exp (↑Real.pi * Complex.I * x) -
                                                  Complex.exp (-(↑Real.pi * Complex.I * x))))
                                            p ((fun (a w : ℝ) => ↑(a + w) + ↑w * Complex.I) a w))
                                        p a w)
                                  n p a w)
                          3 (↑p) (1 / 2))).re)
            (√(t / (2 * Real.pi)) - ↑⌊√(t / (2 * Real.pi))⌋₊) /
          √(t / (2 * Real.pi)))
 ∀ (a b : ℝ), a ≤ b → 32 * Real.pi ≤ a → A a * A b < 0 → (25 / 4 * (a / (2 * Real.pi)) ^ (-(5 / 4) : ℝ) + 1 / 32 * (a / (2 * Real.pi)) ^ (-(15 / 4) : ℝ)) < |A a| → (25 / 4 * (b / (2 * Real.pi)) ^ (-(5 / 4) : ℝ) + 1 / 32 * (b / (2 * Real.pi)) ^ (-(15 / 4) : ℝ)) < |A b| → ∃ t ∈ Set.Ioo a b, riemannZeta (1 / 2 + Complex.I * t) = 0 := by sorry
