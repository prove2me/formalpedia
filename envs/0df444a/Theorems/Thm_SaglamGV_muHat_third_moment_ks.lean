-- Prove2me | Theorems.Thm_SaglamGV_muHat_third_moment_ks
-- name    : SaglamGV.muHat_third_moment_ks
-- status  : Open
-- author  : @parclytaxel
-- created : 2026-11-14T11:38:21.474484+00:00
-- url     : https://prove2.me/theorems/a3951350-fa32-4117-84f6-d92dacc22951
-- title:
--   Finite third-moment estimate for the punctured-ball Fourier transform
-- statement:
--   Let $n\ge2$ and $1\le w\le n/2$. Write $B=\{x\in\mathbb F_2^n:1\le |x|\le w\}$, $V=|B|$, $\mu=1_B/V$, and $\rho=w/n$. With the unnormalized Fourier transform and uniform average over the cube,
--   $$V\,\mathbb E_y|\widehat\mu(y)|^3\le\sqrt{n+1}\,2^{-n\gamma(\rho)}.$$
--   Here $\gamma$ is the explicit Kirshner–Samorodnitsky entropy gap defined in `SaglamGV.gammaKS`. This finite-parameter estimate isolates the spectral moment input to Lemma 3.1, before choosing an asymptotic regime.
--
--   **Formalization Note.** This is the displayed third-moment specialization in Appendix A combined with Parseval and the explicit binomial volume lower bound. Retaining the factor $\sqrt{n+1}$ replaces the source's $2^{O(\lg n)}$ by a concrete bound; it does not assert a sharper asymptotic rate.
-- source:
--   M. Saglam, Linear codes exceeding the Gilbert–Varshamov bound, STOC 2027 submission manuscript (held version sha256 ac6f2bba913aa15cfec8dda07a8e9e37b7186e145fef4719cb623dd04d15baa3), Appendix A, pp.6–7; https://mnsaglam.com/papers/linear-codes.pdf. Uses Kirshner–Samorodnitsky, IEEE Trans. Inf. Theory 67.6 (2021), Corollary 1.4 and Theorem 1.5, doi:10.1109/TIT.2021.3071597.

import Mathlib
import Definitions.Def_SaglamGV_Fourier
import Definitions.Def_SaglamGV_Analytic
import Definitions.Def_SelectiveDPT_H2

theorem SaglamGV.muHat_third_moment_ks (n w : ℕ) (hn : 2 ≤ n) (hw : 1 ≤ w)
    (hwn : 2 * w ≤ n) :
    (SaglamGV.vol n (w + 1) : ℝ) *
        SaglamGV.avgY (fun y ↦ |SaglamGV.muHat n (w + 1) y| ^ 3) ≤
      Real.sqrt ((n : ℝ) + 1) * (2 : ℝ) ^ (-(n : ℝ) * SaglamGV.gammaKS ((w : ℝ) / n)) := by sorry
