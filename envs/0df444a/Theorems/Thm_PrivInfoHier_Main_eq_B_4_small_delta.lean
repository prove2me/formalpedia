-- Prove2me | Theorems.Thm_PrivInfoHier_Main_eq_B_4_small_delta
-- name    : PrivInfoHier.Main.eq_B_4_small_delta
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-11T16:25:16.916929+00:00
-- url     : https://prove2.me/theorems/4357c15c-0f0c-4cbc-9a3c-0e69bfb32adb
-- title:
--   §B.1, Eq. (B.4) for $\delta\le 1-1/e$ (corrected: (B.4) as printed fails for $\delta>1-1/e$)
-- statement:
--   **Source** (App. B.1, p. 18, (B.4)): for $\theta, \delta \in (0, 1)$, $\dfrac{1 - \delta - 1/e}{\log(1/(1 - \theta))} \ge \dfrac{1 - \theta}{\theta}\left(\dfrac{e - 1}{e} - \delta\right)$, using $-\log(1 - \theta) \le \theta/(1 - \theta)$.
--
--   **Variant:** the same inequality for $\theta \in (0, 1)$ and $0 < \delta \le 1 - 1/e$.
--
--   **Difference:** the added hypothesis $\delta \le 1 - 1/e$, which makes the common factor $(e - 1)/e - \delta$ nonnegative so that multiplying $1/\log(1/(1 - \theta)) \ge (1 - \theta)/\theta$ by it preserves the inequality. For $\delta > 1 - 1/e$ the final bound of Theorem 3.2 is negative and needs no chain.
-- source:
--   Taylor, Vippathalla, Coon, An Information Hierarchy of Privacy Filters and Odometers, arXiv:2611.03130 (held version, sha256 77181933…), p. 18 (PDF 20), App. B.1, Eq. (B.4) (corrected)

import Mathlib

namespace PrivInfoHier.Main

theorem eq_B_4_small_delta (θ δ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 - 1 / Real.exp 1) :
    ((1 - θ) / θ) * ((Real.exp 1 - 1) / Real.exp 1 - δ)
      ≤ (1 - δ - 1 / Real.exp 1) / Real.log (1 / (1 - θ)) := by sorry

end PrivInfoHier.Main
