-- Prove2me | Theorems.Thm_RamareAnalytic_harmonic_convolution_error_le
-- name    : RamareAnalytic.harmonic_convolution_error_le
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-19T20:45:48.683516+00:00
-- url     : https://prove2.me/theorems/c5e5cedf-d538-4888-b726-db041653e0b7
-- title:
--   A quantitative error bound for finite harmonic convolutions
-- statement:
--   Let $h:\mathbb N\to\mathbb R$ satisfy $h(0)=0$, $\sum_{d\ge0}h(d)=1$, and convergence of both the logarithmic moment $\sum h(d)\log d$ and the weighted absolute moment $M=\sum |h(d)|d^{2/5}$. As in Lean, the zero-index logarithm is totalized to zero and contributes nothing. Write $\gamma$ for the Euler–Mascheroni constant and $H_m=\sum_{j=1}^m 1/j$, with $H_0=0$. For every positive real $N$,
--
--   $$\left|\sum_{d=1}^{\lfloor N\rfloor}h(d)H_{\lfloor N/d\rfloor}
--   -\left(\log N+\gamma-\sum_{d\ge0}h(d)\log d\right)\right|
--   \le\frac45 N^{-2/5}M.$$
--
--   The estimate transfers a uniform harmonic remainder bound, valid also for arguments below one, to a finite convolution. The mass and moment conditions are explicit assumptions on the coefficient sequence; their verification for the squarefree-totient correction remains a separate task. The exponent and constant are an auxiliary choice in this formal development, not values transcribed from the paper.
-- source:
--   O. Ramaré, On Shnirelman's constant, Ann. Scuola Norm. Sup. Pisa 22 (1995), 645–706, printed pp.656–659, Lemma 3.2 and equations (3.7)–(3.8). https://www.numdam.org/item/ASNSP_1995_4_22_4_645_0/ . Formal reconstruction supporting the existing large-range target https://prove2.me/theorems/017351d0-907f-4262-b614-6850111f1ff0 . General error-transfer mechanism: Lemma 3.2, pp.656–657. Uses the uniform auxiliary estimate https://prove2.me/theorems/d78a0b00-1390-4efd-a5c6-1b3792b65d72 , re-proved in the submitted source. No new analytic principle or optimality is claimed.

import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false
open scoped BigOperators

theorem RamareAnalytic.harmonic_convolution_error_le (h : ℕ → ℝ) (h0 : h 0 = 0)
    (hmass : HasSum h 1)
    (hlog : Summable (fun d : ℕ => h d * Real.log (d : ℝ)))
    (hweight : Summable (fun d : ℕ => |h d| * (d : ℝ) ^ (2 / 5 : ℝ)))
    (N : ℝ) (hN : 0 < N) :
    |(∑ d ∈ Finset.Icc 1 ⌊N⌋₊,
        h d * (harmonic ⌊N / (d : ℝ)⌋₊ : ℝ)) -
        (Real.log N + Real.eulerMascheroniConstant -
          ∑' d : ℕ, h d * Real.log (d : ℝ))| ≤
      (4 / 5 : ℝ) * N ^ (-(2 / 5 : ℝ)) *
        ∑' d : ℕ, |h d| * (d : ℝ) ^ (2 / 5 : ℝ) := by sorry
