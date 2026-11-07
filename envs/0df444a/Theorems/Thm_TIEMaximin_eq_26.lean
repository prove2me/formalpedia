-- Prove2me | Theorems.Thm_TIEMaximin_eq_26
-- name    : TIEMaximin.eq_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:44:12.038508+00:00
-- url     : https://prove2.me/theorems/1ec30f09-b404-478f-8ee4-8c6b5c725b47
-- title:
--   Equations (25), (26) — Case 2: few nominations outside $P_{n-1}$, and $d_i\le 2a_i+1$
-- statement:
--   Let $m\ge n\ge2$, $\alpha=1/6$, $v$ a nonnegative profile, and suppose some agent retains a non-nominated good: $h_{jg}>0$ for some $j$ and $g\notin T_j$. Then
--
--   $$s=\sum_{g\in M\setminus P_{n-1}}f_g=\sum_{g\in P_{n-1}}(n-f_g)<n-1,$$
--
--   and every deficient agent $i$ satisfies
--
--   $$d_i\le2a_i+1.$$
--
--   This is Case 2 of the proof of (19).
--
--   Differences from the source:
--   - encoding: counts s and n − f_g → integers (ℤ); reason: no truncated subtraction
--   - encoding: agents N, goods M, nonnegative additive valuations → `Fin n`, `Fin m` (0-based), real matrices with the hypothesis `Nonneg`, bundle value `valOf`; reason: Lean convention; same instances
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), §5.2.2, eqs. (25), (26), p.26

import Mathlib
import Definitions.Def_TIEMaximin_Basic
import Definitions.Def_TIEMaximin_Comparison

namespace TIEMaximin

/-- **Equations (25), (26)** (§5.2.2, p.26). In Case 2 (some agent retains a non-nominated good), the
number of nominations outside `P_{n−1}` is `s = Σ_{g∉P_{n−1}} f_g = Σ_{g∈P_{n−1}} (n − f_g) < n −
1` (25), and every deficient agent `i` has `d_i ≤ 2a_i + 1` (26).

arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…, §5.2.2, eqs. (25), (26), p.26.

**Formalization Note.** `α = 1/6`. The case hypothesis is `∃ j g, h_jg > 0 ∧ g ∉ T_j` (p.24). `n -
1` is natural subtraction under `2 ≤ n`. The counts in (25) are integers. -/
theorem eq_26 {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) (v : Fin n → Fin m → ℝ) (hv : Nonneg v)
    (hcase : ∃ j g, 0 < hRet (1 / 6) v j g ∧ g ∉ topSet v j) :
    ((∑ g ∈ Finset.univ \ prefixP v (n - 1), (nom v g : ℤ)) =
        ∑ g ∈ prefixP v (n - 1), ((n : ℤ) - (nom v g : ℤ))) ∧
    (∑ g ∈ Finset.univ \ prefixP v (n - 1), (nom v g : ℤ)) < (n : ℤ) - 1 ∧
    ∀ i, IsDeficient (1 / 6) v i → dCost (1 / 6) v i ≤ 2 * aDef (1 / 6) v i + 1 := by sorry

end TIEMaximin
