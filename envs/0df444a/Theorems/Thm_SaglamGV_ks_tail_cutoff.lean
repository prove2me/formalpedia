-- Prove2me | Theorems.Thm_SaglamGV_ks_tail_cutoff
-- name    : SaglamGV.ks_tail_cutoff
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-14T11:38:28.293862+00:00
-- url     : https://prove2.me/theorems/d44dfaa3-1f23-449e-ac50-f96d0901990c
-- title:
--   Numerical cutoff estimates for the Hamming-ball entropy tail
-- statement:
--   Fix $\varepsilon>0$. There are $L>0$ and an integer $N_0\ge2$ such that, whenever $n\ge N_0$ and $L\lg n\le w\le(1/2-\varepsilon)n$, the integers and real numbers
--   $$k=\left\lceil\frac{n\lg n}{w}\right\rceil,\qquad u=\frac{k}{n},\qquad\rho=\frac wn$$
--   satisfy all three estimates
--   $$u\le\tfrac12-\sqrt{\rho(1-\rho)},\qquad\sqrt{n+1}\,e^{-2wu}\le\frac1n,$$
--   $$n(H_2(u)-1)\le-n+\frac{2n\lg n}{w}\lg\!\left(\frac{ew}{\lg n}\right).$$
--   Logarithms denoted by $\lg$ are base two, and $H_2$ is binary entropy in bits. This purely numerical lemma separates the rounding and entropy estimates from the spectral theorem in Appendix A.
--
--   **Formalization Note.** The cutoff is exactly the rounded cutoff used on p.7. The asymptotic regime is expressed uniformly by $L,N_0$, matching the parent milestone. The natural-number ceiling agrees with the ordinary ceiling on this positive range.
-- source:
--   M. Saglam, Linear codes exceeding the Gilbert–Varshamov bound, STOC 2027 submission manuscript (held version sha256 ac6f2bba913aa15cfec8dda07a8e9e37b7186e145fef4719cb623dd04d15baa3), Appendix A, pp.6–7; https://mnsaglam.com/papers/linear-codes.pdf. Uses Kirshner–Samorodnitsky, IEEE Trans. Inf. Theory 67.6 (2021), Corollary 1.4 and Theorem 1.5, doi:10.1109/TIT.2021.3071597.

import Mathlib
import Definitions.Def_SaglamGV_Fourier
import Definitions.Def_SaglamGV_Analytic
import Definitions.Def_SelectiveDPT_H2

theorem SaglamGV.ks_tail_cutoff (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ n w : ℕ, N₀ ≤ n → L * Real.logb 2 n ≤ w →
        (w : ℝ) ≤ (1 / 2 - ε) * n →
        let k : ℕ := ⌈(n : ℝ) * Real.logb 2 n / w⌉₊
        (k : ℝ) / n ≤ 1 / 2 -
            Real.sqrt (((w : ℝ) / n) * (1 - (w : ℝ) / n)) ∧
          Real.sqrt ((n : ℝ) + 1) * Real.exp (-2 * w * ((k : ℝ) / n)) ≤
            1 / (n : ℝ) ∧
          (n : ℝ) * (SelectiveDPT.H2 ((k : ℝ) / n) - 1) ≤
            -(n : ℝ) + 2 * n * Real.logb 2 n / w *
              Real.logb 2 (Real.exp 1 * w / Real.logb 2 n) := by sorry
