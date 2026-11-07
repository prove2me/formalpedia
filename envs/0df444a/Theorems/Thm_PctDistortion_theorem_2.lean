-- Prove2me | Theorems.Thm_PctDistortion_theorem_2
-- name    : PctDistortion.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:43:39.982713+00:00
-- url     : https://prove2.me/theorems/41fba252-2319-4193-99d8-21dc7b1658ca
-- title:
--   Theorem 2 — a small ABC value yields an election where every ABCα-maximal lottery has distortion $>3+2/s$
-- statement:
--   Let $\alpha\in[1/2,1)$, $s=\lfloor1/(1-\alpha)\rfloor$, and let $H=(V_H,E_H)\in M_\alpha$ be an α-majority digraph with $\nu(\mathcal G^{ABC}_H)<1-2/s$. Then there exists an election $\mathcal E$ such that
--   $$\mathrm{dist}^\alpha_{\mathcal E}(a)>3+\frac2s\qquad\text{for all }a\in\mathrm{ABC}^\alpha(\mathcal E).$$
--   For $\alpha<2/3$ ($s=2$) the hypothesis cannot hold, by Proposition 3. This is the "only if" half of Theorem B.
--
--   Differences from the source:
--   - encoding: finite elections with n voters and m candidates → finite nonempty voter and candidate types; reason: the percentile cost and the lotteries presuppose n, m ≥ 1; with n = 0 the cost is undefined and with m = 0 there is no lottery
--   - encoding: ν = Alice's payoff under any equilibrium → Alice's maximin value (abcValue); reason: equal by the minimax theorem; the maximin value exists for every finite game
--   - encoding: ratio cost(p)/min_c cost(c) in the reals → ratio in [0, ∞] with x/0 = ∞ (x > 0) and 0/0 = 0; reason: the ratio is undefined when the optimal cost is 0; this convention makes dist ≤ B equivalent to cost(p) ≤ B·min cost for every consistent metric
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Theorem 2, p.12 (proof p.16)

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_PctDistortion_distortion
import Definitions.Def_PctDistortion_alphaMajority
import Definitions.Def_PctDistortion_abcValue
import Definitions.Def_PctDistortion_abcMaximal

set_option autoImplicit false

namespace PctDistortion

/-- **Theorem 2** (distortion lower bound from a small game value). Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Theorem 2, p.12: let
`H ∈ M_α` with `ν(G^ABC_H) < 1 − 2/s`, where `s = ⌊1/(1 − α)⌋`. Then there exists an election `E`
such that `dist^α_E(a) > 3 + 2/s` for all `a ∈ ABCα(E)`.

**Formalization Note.** For every `α ∈ [1/2, 1)`; for `α < 2/3` (`s = 2`) the hypothesis cannot
hold (p.12). The election has finite nonempty voter and candidate sets. -/
theorem theorem_2 (α : ℝ) (hα₁ : 1 / 2 ≤ α) (hα₂ : α < 1) {VH : Type} [Fintype VH] [Nonempty VH]
    (H : Digraph VH) (hH : IsAlphaMajority α H)
    (hν : abcValue H < 1 - 2 / (⌊1 / (1 - α)⌋₊ : ℝ)) :
    ∃ (V C : Type) (_ : Fintype V) (_ : Nonempty V) (_ : Fintype C) (_ : Nonempty C)
      (E : Election V C), ∀ a ∈ abcAlphaMaximal α E,
        ENNReal.ofReal (3 + 2 / (⌊1 / (1 - α)⌋₊ : ℝ)) < distortion α E a := by sorry

end PctDistortion
