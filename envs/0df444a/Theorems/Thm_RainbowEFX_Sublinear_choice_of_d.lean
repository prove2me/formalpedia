-- Prove2me | Theorems.Thm_RainbowEFX_Sublinear_choice_of_d
-- name    : RainbowEFX.Sublinear.choice_of_d
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:28.633809+00:00
-- url     : https://prove2.me/theorems/299150de-9679-4bd7-9fad-992fdeb413af
-- title:
--   p. 14 — d = ⌈(n/ε)^(1/5)⌉ is the least d ≥ 1 with 2n/(ε · d) ≤ 2d⁴, and 4d⁴ < 64(n/ε)^(4/5)
-- statement:
--   Let $n\ge 1$ be an integer and $0<\varepsilon\le1/2$, and put
--   $$
--   d=\big\lceil (n/\varepsilon)^{1/5}\big\rceil .
--   $$
--   Then $d\ge1$, $d$ is the smallest positive integer with $\dfrac{2n}{\varepsilon\cdot d}\le 2d^4$, and
--   $$
--   4d^4<64\,(n/\varepsilon)^{4/5}.
--   $$
--
--   With the count at termination, $|P|\le 2\cdot\max(2n/(\varepsilon d),2d^4)=4d^4<64(n/\varepsilon)^{4/5}$, which is Theorem 1.
--
--   **Formalization Note** $(n/\varepsilon)^{1/5}$ is the real power `Real.rpow` and $\lceil\cdot\rceil$ is `Nat.ceil`.
-- source:
--   Chaudhury, Garg, Mehlhorn, Mehta, Misra, Improving EFX Guarantees through Rainbow Cycle Number, arXiv:2103.01628v1, p. 14, "Putting it together", choice of d for the algorithmic result

import Mathlib
import Definitions.Def_RainbowEFX_Sublinear_Setting

namespace RainbowEFX.Sublinear

open LittleCharity.EFX

theorem choice_of_d (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) :
    let d := ⌈((n : ℝ) / ε) ^ ((1 : ℝ) / 5)⌉₊
    (1 ≤ d ∧ 2 * (n : ℝ) / (ε * d) ≤ 2 * (d : ℝ) ^ 4 ∧
      ∀ d' : ℕ, 1 ≤ d' → 2 * (n : ℝ) / (ε * d') ≤ 2 * (d' : ℝ) ^ 4 → d ≤ d') ∧
    4 * (d : ℝ) ^ 4 < 64 * ((n : ℝ) / ε) ^ ((4 : ℝ) / 5) := by sorry

end RainbowEFX.Sublinear
