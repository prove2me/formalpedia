-- Prove2me | Theorems.Thm_RHHeight1000_gram664_explicit_rs_sign_certificate
-- name    : RHHeight1000.gram664_explicit_rs_sign_certificate
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-19T17:06:53.090343+00:00
-- url     : https://prove2.me/theorems/40cd93d5-852a-49a0-8744-661e38ed7286
-- title:
--   Riemann–Siegel sign and error certificate at 1020.266 and 1021.497
-- statement:
--   Let $A(t)$ be the explicit Riemann–Siegel approximant in the formal statement, with second-order Stirling phase and constant and linear correction terms. Put $$E(t)=\frac{25}{4}(t/(2\pi))^{-5/4}+\frac{1}{32}(t/(2\pi))^{-15/4},\quad a=1020.266,\quad b=1021.497.$$ Then $$32\pi\le a,\qquad A(a)A(b)<0,\qquad E(a)<|A(a)|,\qquad E(b)<|A(b)|.$$ The exact decimal endpoints are rational numbers. These are the numerical hypotheses needed by the analytic sign-transfer theorem for this interval.
-- source:
--   Salvatore Mercuri and Bhavik Mehta, smmercuri/zeta, commit 3dab6480a82f1bfc5de0a59550e279cf50490033, Apache-2.0; numeric certificate Zeta.Certificates.Gram.z10_1_cert. Dependency pruning and reducible abbreviation compression preserve the original proof; source authorship notices retained.

import Mathlib
open scoped Real BigOperators
open MeasureTheory

theorem RHHeight1000.gram664_explicit_rs_sign_certificate :
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
 32 * Real.pi ≤ (1020.26600 : ℝ) ∧ A (1020.26600 : ℝ) * A (1021.49700 : ℝ) < 0 ∧ (25 / 4 * ((1020.26600 : ℝ) / (2 * Real.pi)) ^ (-(5 / 4) : ℝ) + 1 / 32 * ((1020.26600 : ℝ) / (2 * Real.pi)) ^ (-(15 / 4) : ℝ)) < |A (1020.26600 : ℝ)| ∧ (25 / 4 * ((1021.49700 : ℝ) / (2 * Real.pi)) ^ (-(5 / 4) : ℝ) + 1 / 32 * ((1021.49700 : ℝ) / (2 * Real.pi)) ^ (-(15 / 4) : ℝ)) < |A (1021.49700 : ℝ)| := by sorry
