-- Prove2me | Theorems.Thm_PctDistortion_corollary_3
-- name    : PctDistortion.corollary_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:43:24.468599+00:00
-- url     : https://prove2.me/theorems/e5c9fda6-13c0-45a3-8273-31a4644bd123
-- title:
--   Corollary 3 — ABCα-Maximal Lotteries has distortion at most $4-1/m$
-- statement:
--   For every $\alpha\in[1/2,1)$ and every election $\mathcal E=(V,C,\vec\succ)$ with $m=|C|$ candidates, every ABCα-maximal lottery $a\in\mathrm{ABC}^\alpha(\mathcal E)$ satisfies
--   $$\mathrm{dist}^\alpha_{\mathcal E}(a)\le 4-\frac1m.$$
--   That is, ABCα-Maximal Lotteries has α-percentile distortion at most $4-1/m$, whichever ABCα-maximal lottery it returns. For $\alpha=1/2$ this improves the bound 4 of Anshelevich and Postl for Uncovered Set Min-Cover.
--
--   Differences from the source:
--   - encoding: finite elections with n voters and m candidates → finite nonempty voter and candidate types; reason: the percentile cost and the lotteries presuppose n, m ≥ 1; with n = 0 the cost is undefined and with m = 0 there is no lottery
--   - reading: the rule ABCα-Maximal Lotteries has distortion at most … → every a ∈ ABCα(E) has distortion at most …; reason: the rule returns an arbitrary element of ABCα(E), so the bound holds for every choice exactly when it holds for every element
--   - encoding: ratio cost(p)/min_c cost(c) in the reals → ratio in [0, ∞] with x/0 = ∞ (x > 0) and 0/0 = 0; reason: the ratio is undefined when the optimal cost is 0; this convention makes dist ≤ B equivalent to cost(p) ≤ B·min cost for every consistent metric
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Corollary 3, p.17

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_PctDistortion_distortion
import Definitions.Def_PctDistortion_abcMaximal

set_option autoImplicit false

namespace PctDistortion

/-- **Corollary 3** (distortion `4 − 1/m`). Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Corollary 3, p.17: for every `α ∈ [1/2, 1)`,
ABCα-Maximal Lotteries has α-percentile distortion at most `4 − 1/m`.

Stated for every election `E` with `m = |C|` candidates and every ABCα-maximal lottery
`a ∈ ABCα(E)`, so it holds for every way of choosing the "arbitrary" lottery of the rule. -/
theorem corollary_3 (α : ℝ) (hα₁ : 1 / 2 ≤ α) (hα₂ : α < 1) {V C : Type} [Fintype V] [Nonempty V]
    [Fintype C] [Nonempty C] (E : Election V C) :
    ∀ a ∈ abcAlphaMaximal α E,
      distortion α E a ≤ ENNReal.ofReal (4 - 1 / (Fintype.card C : ℝ)) := by sorry

end PctDistortion
