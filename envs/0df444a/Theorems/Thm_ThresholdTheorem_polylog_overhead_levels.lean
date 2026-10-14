-- Prove2me | Theorems.Thm_ThresholdTheorem_polylog_overhead_levels
-- name    : ThresholdTheorem.polylog_overhead_levels
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T01:02:49.102755+00:00
-- url     : https://prove2.me/theorems/e0eb1dd8-f6c2-4224-9257-bb2c1fa98018
-- title:
--   Polylogarithmic overhead of the number of concatenation levels
-- statement:
--   **Polylogarithmic overhead.** Let $c>0$, $p\ge0$ with $cp<1$, and $d\in\mathbb N$. There is a constant $A$ such that for every integer $g\ge1$ and every $0<\varepsilon<1$ there is a number of levels $k$ with
--
--   $$g\cdot\frac{(c\,p)^{2^{k}}}{c}\;\le\;\varepsilon\qquad\text{and}\qquad d^{k}\;\le\;A\,\Big(\log\frac{g}{\varepsilon}+1\Big)^{\lceil\log_2 d\rceil}.$$
--
--   With $g$ the size of the circuit to be simulated, the first inequality says that $k$ levels of concatenation bring the total failure probability below $\varepsilon$, and the second that the resulting size overhead $d^k$ is only polylogarithmic in $g/\varepsilon$, as claimed in the threshold theorem.
-- source:
--   Wikipedia, "Threshold theorem" (revision oldid=1360742213, https://en.wikipedia.org/w/index.php?title=Threshold_theorem&oldid=1360742213), section "Explanation"; the boxed statement is quoted there from M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum Information, 10th anniversary ed., Cambridge University Press, p. 481.

import Mathlib
import Definitions.Def_threshold_theorem_noise_model

open ThresholdTheorem

namespace ThresholdTheorem
theorem polylog_overhead_levels (c p : ℝ) (d : ℕ) (hc : 0 < c) (hp : 0 ≤ p)
    (hcp : c * p < 1) :
    ∃ A : ℝ, ∀ (g : ℕ) (ε : ℝ), 1 ≤ g → 0 < ε → ε < 1 → ∃ k : ℕ,
      g * ((c * p) ^ (2 ^ k) / c) ≤ ε ∧
        (d : ℝ) ^ k ≤ A * (Real.log (g / ε) + 1) ^ Nat.clog 2 d := by sorry
end ThresholdTheorem
