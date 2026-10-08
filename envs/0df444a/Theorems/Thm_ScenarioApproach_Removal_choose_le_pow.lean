-- Prove2me | Theorems.Thm_ScenarioApproach_Removal_choose_le_pow
-- name    : ScenarioApproach.Removal.choose_le_pow
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T05:39:43.416984+00:00
-- url     : https://prove2.me/theorems/330c5f49-df80-4a0b-9ef3-ba72e5e31688
-- title:
--   Eq. (3.17) — $\binom{k+d-1}{k} = \frac{(k+d-1)!}{k!(d-1)!} \le (k+d-1)^{d-1}$
-- statement:
--   For all natural numbers $k \ge 0$ and $d \ge 1$,
--
--   $$
--   \binom{k+d-1}{k} = \frac{(k+d-1)!}{k!\,(d-1)!} \le (k+d-1)^{d-1}.
--   $$
--
--   This elementary estimate controls the combinatorial factor in the bound (3.13) of Theorem 3.9 and is used in the derivation of the explicit violation level $\varepsilon_k$ of Theorem 1.2.
--
--   **Formalization Note** The equality is stated in $\mathbb R$ (factorials cast to reals) and the inequality in $\mathbb N$, with $0^0 = 1$. The hypothesis $d \ge 1$ makes the natural-number subtractions $k+d-1$ and $d-1$ exact.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 48, Eq. (3.17)

import Mathlib

namespace ScenarioApproach.Removal

theorem choose_le_pow (k d : ℕ) (hd : 1 ≤ d) :
    ((k + d - 1).choose k : ℝ) =
        ((k + d - 1).factorial : ℝ) / ((k.factorial : ℝ) * ((d - 1).factorial : ℝ)) ∧
      (k + d - 1).choose k ≤ (k + d - 1) ^ (d - 1) := by sorry

end ScenarioApproach.Removal
