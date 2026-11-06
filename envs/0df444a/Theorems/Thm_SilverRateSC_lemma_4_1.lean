-- Prove2me | Theorems.Thm_SilverRateSC_lemma_4_1
-- name    : SilverRateSC.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:46:00.003208+00:00
-- url     : https://prove2.me/theorems/e14585e2-3193-4d2c-bb9c-8596b2ede5a1
-- title:
--   Lemma 4.1 — bounds for a maximizing checkpoint set
-- statement:
--   Fix a positive integer $m$, $a\ge8$, $1\le c\le2$, $p=p(c)$, a block $H=(h_1,\dots,h_r)$ of nonnegative stepsizes with $1\le r\le m$, and an incoming tail sum $w\ge0$; let $s_i$, $s_{\rm tail}$, $b_i$ be as in (17). There is an absolute constant $C_b$ such that:
--   1. if the empty set maximizes the score (18), then $w+\sum_{j=1}^rh_j\le C_b(w+am^p)$;
--
--   and for every nonempty maximizing set $T=\{t_1<\dots<t_k\}$:
--
--   2. $c\sum_{i=1}^k(a+s_i+8)\le C_b(w+am^p)$ and $s_{\rm tail}\le C_b\,a\,m^p$;
--   3. for every $1\le i<k$, $\displaystyle\frac1{b_i-8}\le\frac2{a+s_i+8}+\frac2{a+s_{i+1}+8}$;
--   4. the last checkpoint satisfies $b_k-8\ge c(a+s_k+8)$.
--
--   These estimates keep the gaps short relative to $\kappa$ and bound the relative threshold left by the last checkpoint.
--
--   Differences from the source:
--   - encoding: absolute constant C_b; the setting of §4.1 (m ≥ 1, 1 ≤ r ≤ m, a ≥ 8, 1 ≤ c ≤ 2, w ≥ 0, h_j ≥ 0) → ∃ C_b quantified before a, c, m, r, w, h; the setting as hypotheses; reason: order of quantifiers expresses that C_b is absolute
--   - encoding: consecutive checkpoints t_i < t_{i+1}; the last checkpoint t_k → elements t < t' of T with no element of T strictly between them; the element of T above all others; reason: same checkpoints
--   - encoding: block H and checkpoint sets → h : ℕ → ℝ read at positions 1, …, r; T : Finset ℕ; s_i = gapSum, s_tail = tailSum; reason: same data
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), Lemma 4.1, pp.17–18; setting §4.1, p.17

import Mathlib
import Definitions.Def_SilverRateSC_pOf
import Definitions.Def_SilverRateSC_score

namespace SilverRateSC

/-- **Lemma 4.1 (Bounds for a maximizing checkpoint set).** Fix a positive integer `m`,
`a ≥ 8`, `1 ≤ c ≤ 2`, `p = p(c)`, a block of `1 ≤ r ≤ m` nonnegative stepsizes `h_1, …, h_r` and
an incoming tail sum `w ≥ 0`. There is an absolute constant `C_b` with the following properties;
(ii)–(iv) hold for every nonempty maximizing set `T = {t_1 < ⋯ < t_k}`.
(i) If the empty set maximizes (18), then `w + ∑_{j=1}^r h_j ≤ C_b(w + a m^p)`.
(ii) `c ∑_{i=1}^k (a + s_i + 8) ≤ C_b(w + a m^p)` and `s_tail ≤ C_b a m^p`.
(iii) For every `1 ≤ i < k`, `1/(b_i − 8) ≤ 2/(a + s_i + 8) + 2/(a + s_{i+1} + 8)`.
(iv) The last checkpoint satisfies `b_k − 8 ≥ c(a + s_k + 8)`.

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, Lemma 4.1, pp. 17–18 (setting §4.1, p. 17).

**Formalization Note** `C_b` is quantified before `a, c, m, r, w, H`. Consecutive checkpoints
`t_i < t_{i+1}` are two elements of `T` with no element of `T` strictly between them; the last
checkpoint is the element of `T` above all others. `s_i` is `gapSum w h T t_i`, `s_tail` is
`tailSum r h T`, `m^p` is a real power. -/
theorem lemma_4_1 :
    ∃ Cb : ℝ, ∀ a c : ℝ, 8 ≤ a → 1 ≤ c → c ≤ 2 → ∀ m r : ℕ, 1 ≤ m → 1 ≤ r → r ≤ m →
      ∀ w : ℝ, 0 ≤ w → ∀ h : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 r, 0 ≤ h j) →
        (IsMaximizing a c w r h ∅ →
          w + ∑ j ∈ Finset.Icc 1 r, h j ≤ Cb * (w + a * (m : ℝ) ^ pOf c)) ∧
        ∀ T : Finset ℕ, T.Nonempty → IsMaximizing a c w r h T →
          (c * ∑ t ∈ T, (a + gapSum w h T t + 8) ≤ Cb * (w + a * (m : ℝ) ^ pOf c) ∧
            tailSum r h T ≤ Cb * a * (m : ℝ) ^ pOf c) ∧
          (∀ t ∈ T, ∀ t' ∈ T, t < t' → (∀ u ∈ T, ¬ (t < u ∧ u < t')) →
            1 / (h t - 8) ≤ 2 / (a + gapSum w h T t + 8) + 2 / (a + gapSum w h T t' + 8)) ∧
          (∀ t ∈ T, (∀ u ∈ T, u ≤ t) → c * (a + gapSum w h T t + 8) ≤ h t - 8) := by sorry

end SilverRateSC
