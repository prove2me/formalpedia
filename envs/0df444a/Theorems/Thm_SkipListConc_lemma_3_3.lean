-- Prove2me | Theorems.Thm_SkipListConc_lemma_3_3
-- name    : SkipListConc.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:52:56.126086+00:00
-- url     : https://prove2.me/theorems/c1fdfdc6-c847-46f5-b17b-2eadbcfae796
-- title:
--   Lemma 3.3 — tails and shifts of $\beta$-thick distributions are $\beta$-thick
-- statement:
--   Let $\mu$ be a $\beta$-thick distribution on the positive integers.
--
--   1. Let $r_0\ge1$ with $T=\sum_{r\ge r_0}\mu_r>0$. The distribution $\mu$ restricted to $[r_0,\infty)$ and renormalized, $\mu'_r=\mu_r/T$ for $r\ge r_0$ and $\mu'_r=0$ for $r<r_0$, is $\beta$-thick.
--   2. Let $d\ge0$ be an integer. The distribution $\mu$ shifted up by $d$, $\mu''_r=\mu_{r-d}$ for $r>d$ and $\mu''_r=0$ for $r\le d$, is $\beta$-thick.
--
--   Differences from the source:
--   - encoding: T = ∑_{r ≥ r0} μ_r → the sum over ℕ of the indicator of {r ≥ r0} times μ; reason: same series
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Lemma 3.3, p.17

import Mathlib
import Definitions.Def_SkipListConc_IsThick

namespace SkipListConc

/-- Lemma 3.3 (tails and shifts of thick distributions) (Kapoor–Tanveer, *Counter-Free
Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript (sha256
f82c3d35…6dab6c), Lemma 3.3, p.17). Let `μ` be `β`-thick.
(i) Let `r₀ ≥ 1` with `T = ∑_{r ≥ r₀} μ_r > 0`. The distribution `μ'_r = μ_r / T` for `r ≥ r₀`,
`μ'_r = 0` for `r < r₀`, is `β`-thick.
(ii) Let `d ≥ 0` be an integer. The distribution `μ''_r = μ_{r−d}` for `r > d`, `μ''_r = 0` for
`r ≤ d`, is `β`-thick. -/
theorem lemma_3_3 (β : ℝ) (μ : ℕ → ℝ) (hμ : IsThick β μ) :
    (∀ r₀ : ℕ, 1 ≤ r₀ → 0 < ∑' r, Set.indicator {r : ℕ | r₀ ≤ r} μ r →
        IsThick β (fun r => if r₀ ≤ r then μ r / ∑' s, Set.indicator {s : ℕ | r₀ ≤ s} μ s
          else 0)) ∧
      ∀ d : ℕ, IsThick β (fun r => if d < r then μ (r - d) else 0) := by sorry

end SkipListConc
