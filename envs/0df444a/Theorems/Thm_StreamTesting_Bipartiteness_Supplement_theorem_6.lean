-- Prove2me | Theorems.Thm_StreamTesting_Bipartiteness_Supplement_theorem_6
-- name    : StreamTesting.Bipartiteness.Supplement.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:03:11.242912+00:00
-- url     : https://prove2.me/theorems/fb67ee04-2d46-4915-a4c2-588f9f8960ac
-- title:
--   Theorem 6 — random-order connectivity testing
-- statement:
--   There is an absolute $C>0$ such that, for all $n,d\ge1$ and $0<\varepsilon\le1$, set $x=\min\{\varepsilon d,1/2\}$. A randomized forward-only neighborhood tester has worst-run bound
--
--   $$q\le\left\lceil\exp\left(C\frac{\log(1/x)}{x}\right)\right\rceil.$$
--
--   It accepts connected graphs and rejects graphs requiring at least $\varepsilon dn$ insertions or deletions to reach a connected graph of maximum degree at most $d$, each with probability at least $2/3$ over independent uniform order and private coins. The bound is independent of $n$, and caps queries at every order and every positive-probability private choice. Degree one and small inputs remain covered. For $0<\varepsilon d\le1/2$ this is the displayed bound of Theorem 6; larger parameters use the source's clamp.
--
--   Differences from the source:
--   - encoding: arbitrary randomized forward-only graph algorithms on n observed labels → input-independent PMFs over the published history policies on Fin n, with actual execution; reason: for fixed n all graph-observation histories are finite, so every private random tape induces such a distribution without a memory or computation bound
--   - encoding: the bound is stated for 0 < epsilon*d <= 1/2, with larger epsilon handled at 1/(2d) → x = min(epsilon*d,1/2) in the single bound exp(C log(1/x)/x); reason: this is exactly the instructed parameter clamp; x is positive and at most 1/2, so division and logarithms are defined
--   - encoding: exponential O bound, made worst-case by Markov truncation → one absolute positive C before every instance and a natural ceiling; reason: the factorial sampling estimates on pp.13–15 give expected queries at most 128 floor(8/x)!/x^2 and 100-fold truncation fits the displayed exponential; reading small inputs completely fits the same bound
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026), citation basis published; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; Theorem 6, printed p.13 / PDF p.13.

import Definitions.Def_StreamTesting_Bipartiteness_Supplement_ConnectivityFarness
import Definitions.Def_StreamTesting_Bipartiteness_Supplement_GraphTesting
import Definitions.Def_StreamTesting_Bipartiteness_QueryCap

namespace StreamTesting.Bipartiteness.Supplement

/-- Theorem 6, p.13, including its stated clamp for epsilon*d > 1/2. -/
theorem theorem_6 :
    ∃ C : ℝ, 0 < C ∧ ∀ n d : ℕ, 1 ≤ n → 1 ≤ d →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      let x : ℝ := min (ε * (d : ℝ)) ((1 : ℝ) / 2)
      ∃ μ : RandomPolicy n,
        QueryCap d μ ⌈Real.exp (C * Real.log (1 / x) / x)⌉₊ ∧
        RandomOrderTester (fun G => G.Connected) (fun G => ConnectivityFar G d ε) d μ := by sorry

end StreamTesting.Bipartiteness.Supplement
