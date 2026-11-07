-- Prove2me | Theorems.Thm_PctDistortion_theorem_1
-- name    : PctDistortion.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:43:30.242799+00:00
-- url     : https://prove2.me/theorems/f399483e-37e3-4cc8-9b05-30fffaa9e219
-- title:
--   Theorem 1 — every ABCα-maximal lottery has distortion at most $4-\nu(\mathcal G^{ABC}_{G^\alpha_{\mathcal E}})$
-- statement:
--   For every election $\mathcal E=(V,C,\vec\succ)$ and percentile $\alpha\in[1/2,1)$, every equilibrium strategy $a\in\mathrm{ABC}^\alpha(\mathcal E)$ satisfies
--   $$\mathrm{dist}^\alpha_{\mathcal E}(a)\le 4-\nu\big(\mathcal G^{ABC}_{G^\alpha_{\mathcal E}}\big).$$
--   A large ABC value of the α-majority digraph therefore certifies low distortion; this is the "if" half of Theorem B.
--
--   Differences from the source:
--   - encoding: finite elections with n voters and m candidates → finite nonempty voter and candidate types; reason: the percentile cost and the lotteries presuppose n, m ≥ 1; with n = 0 the cost is undefined and with m = 0 there is no lottery
--   - encoding: ν = Alice's payoff under any equilibrium → Alice's maximin value (abcValue); reason: equal by the minimax theorem; the maximin value exists for every finite game
--   - encoding: ratio cost(p)/min_c cost(c) in the reals → ratio in [0, ∞] with x/0 = ∞ (x > 0) and 0/0 = 0; reason: the ratio is undefined when the optimal cost is 0; this convention makes dist ≤ B equivalent to cost(p) ≤ B·min cost for every consistent metric
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Theorem 1, p.12 (proof App. D.2, p.35)

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_PctDistortion_distortion
import Definitions.Def_PctDistortion_abcMaximal

set_option autoImplicit false

namespace PctDistortion

/-- **Theorem 1** (distortion `4 − ν`). Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Theorem 1, p.12 (proof App. D.2, p.35): for every
election `E` and `α ∈ [1/2, 1)`, every `a ∈ ABCα(E)` has
`dist^α_E(a) ≤ 4 − ν(G^ABC_{G^α_E})`. -/
theorem theorem_1 (α : ℝ) (hα₁ : 1 / 2 ≤ α) (hα₂ : α < 1) {V C : Type} [Fintype V] [Nonempty V]
    [Fintype C] [Nonempty C] (E : Election V C) :
    ∀ a ∈ abcAlphaMaximal α E,
      distortion α E a ≤ ENNReal.ofReal (4 - abcValue (alphaMajority α E)) := by sorry

end PctDistortion
