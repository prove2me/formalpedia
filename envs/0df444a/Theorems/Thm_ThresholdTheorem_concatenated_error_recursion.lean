-- Prove2me | Theorems.Thm_ThresholdTheorem_concatenated_error_recursion
-- name    : ThresholdTheorem.concatenated_error_recursion
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T01:00:23.552628+00:00
-- url     : https://prove2.me/theorems/44a94398-d0f9-4448-8ff3-cc4c29d34eca
-- title:
--   Recursive error suppression $e_k \le (cp)^{2^k}/c$
-- statement:
--   **Recursive error suppression.** Let $c>0$ and let $(e_k)_{k\ge0}$ be non-negative reals with $e_0\le p$ and
--
--   $$e_{k+1}\;\le\;c\,e_k^{2}\qquad(k\ge 0).$$
--
--   Then for every $k$,
--
--   $$e_k\;\le\;\frac{(c\,p)^{2^k}}{c}.$$
--
--   Here $e_k$ plays the role of the failure probability of a level-$k$ encoded gate. When $p<1/c$ the bound decreases doubly exponentially in the number of levels, which is the source of the threshold $p_{\mathrm{th}}=1/c$.
-- source:
--   Wikipedia, "Threshold theorem" (revision oldid=1360742213, https://en.wikipedia.org/w/index.php?title=Threshold_theorem&oldid=1360742213), section "Explanation"; the boxed statement is quoted there from M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum Information, 10th anniversary ed., Cambridge University Press, p. 481.

import Mathlib
import Definitions.Def_threshold_theorem_noise_model

open ThresholdTheorem

namespace ThresholdTheorem
theorem concatenated_error_recursion (c p : ℝ) (hc : 0 < c) (e : ℕ → ℝ)
    (he0 : e 0 ≤ p) (hnn : ∀ k, 0 ≤ e k) (hrec : ∀ k, e (k + 1) ≤ c * e k ^ 2) (k : ℕ) :
    e k ≤ (c * p) ^ (2 ^ k) / c := by sorry
end ThresholdTheorem
