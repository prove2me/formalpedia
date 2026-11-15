-- Prove2me | Theorems.Thm_SaglamGV_muHat_tail_ks
-- name    : SaglamGV.muHat_tail_ks
-- status  : Open
-- author  : @parclytaxel
-- created : 2026-11-14T11:38:31.669577+00:00
-- url     : https://prove2.me/theorems/0345ffa1-7038-4dfd-87bd-310e8b7213aa
-- title:
--   Finite entropy tail estimate for the punctured-ball Fourier transform
-- statement:
--   Let $n\ge2$, $1\le w\le n/2$, $k\ge0$ be integers, $\rho=w/n$, and $u=k/n$. Suppose
--   $$u\le\tfrac12-\sqrt{\rho(1-\rho)}.$$
--   For the uniform kernel $\mu$ on the punctured Hamming ball of radius $w$, of size $V$, the unnormalized Fourier transform satisfies
--   $$\Pr_y\!\left[|\widehat\mu(y)|>\sqrt{n+1}\,e^{-2wu}\right]\le2^{n(H_2(u)-1)}.$$
--   Probabilities are uniform on $\mathbb F_2^n$ and include $y=0$. This is a finite-parameter tail bound that can be applied at any admissible integral cutoff.
--
--   **Formalization Note.** Appendix A's KS threshold is bounded above by $\sqrt{n+1}\,2^{n(T(\rho,u)-H_2(\rho))}\le\sqrt{n+1}\,e^{-2wu}$ using the binomial volume estimate and the displayed bound on $H_2-T$. The strict event above is therefore contained in the source's non-strict threshold event; this is a weakening of that bound.
-- source:
--   M. Saglam, Linear codes exceeding the Gilbert–Varshamov bound, STOC 2027 submission manuscript (held version sha256 ac6f2bba913aa15cfec8dda07a8e9e37b7186e145fef4719cb623dd04d15baa3), Appendix A, pp.6–7; https://mnsaglam.com/papers/linear-codes.pdf. Uses Kirshner–Samorodnitsky, IEEE Trans. Inf. Theory 67.6 (2021), Corollary 1.4 and Theorem 1.5, doi:10.1109/TIT.2021.3071597.

import Mathlib
import Definitions.Def_SaglamGV_Fourier
import Definitions.Def_SaglamGV_Analytic
import Definitions.Def_SelectiveDPT_H2

theorem SaglamGV.muHat_tail_ks (n w k : ℕ) (hn : 2 ≤ n) (hw : 1 ≤ w)
    (hwn : 2 * w ≤ n)
    (hk : (k : ℝ) / n ≤ 1 / 2 -
      Real.sqrt (((w : ℝ) / n) * (1 - (w : ℝ) / n))) :
    SaglamGV.probY (fun y ↦ Real.sqrt ((n : ℝ) + 1) *
        Real.exp (-2 * w * ((k : ℝ) / n)) < |SaglamGV.muHat n (w + 1) y|) ≤
      (2 : ℝ) ^ ((n : ℝ) * (SelectiveDPT.H2 ((k : ℝ) / n) - 1)) := by sorry
