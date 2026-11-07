-- Prove2me | Theorems.Thm_SetMultCost_lemma_7_2
-- name    : SetMultCost.lemma_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:54:52.412362+00:00
-- url     : https://prove2.me/theorems/e5856b29-9a74-4bee-b49e-64a3982d6536
-- title:
--   Lemma 7.2 — bounds for $\tilde q_t$
-- statement:
--   Let $\tilde q_t$ be the convergent denominators of $[0,1,2c,m,m,m^2,m^3,\dots]$, with integers $m\ge2$ and $c\ge1$. For all $t\ge3$,
--
--   $$(2c+1)\,m^{F(t-1)-1}\le\tilde q_t\le2(2c+1)\,m^{F(t-1)-1}.$$
--
--   This locates the convergents, and so the thresholds, of the hard number.
--
--   Differences from the source:
--   - encoding: m unqualified in §7.2 → m ≥ 2, and c ≥ 1; reason: §6.1 fixes "a positive integer m > 1"; at m = 1, c = 2, t = 6 the upper bound fails (q̃₆ = 28 > 10), and a₂ = 2c needs c ≥ 1
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), Lemma 7.2, p.22

import Mathlib
import Definitions.Def_SetMultCost_cfDen
import Definitions.Def_SetMultCost_fibF
import Definitions.Def_SetMultCost_alphaTildeDigits

namespace SetMultCost

/-- **Lemma 7.2 (Bounds for `q̃_t`).** Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), p.22: "For all t ≥ 3, (2c + 1)m^{F(t−1)−1} ≤ eqt ≤ 2 · (2c +
1)m^{F(t−1)−1}."

**Formalization Note.** `m ≥ 2` is §6.1's "positive integer m > 1", inherited by §7.2; at `m = 1`,
`c = 2`, `t = 6` the upper bound fails (`q̃₆ = 28 > 10`). `c ≥ 1` keeps `a₂ = 2c` positive. -/
theorem lemma_7_2 (m c t : ℕ) (hm : 2 ≤ m) (hc : 1 ≤ c) (ht : 3 ≤ t) :
    (2 * (c : ℤ) + 1) * (m : ℤ) ^ (fibF (t - 1) - 1) ≤ cfDen (alphaTildeDigits m c) t ∧
    cfDen (alphaTildeDigits m c) t ≤ 2 * ((2 * (c : ℤ) + 1) * (m : ℤ) ^ (fibF (t - 1) - 1)) := by sorry

end SetMultCost
