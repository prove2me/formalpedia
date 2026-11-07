-- Prove2me | Theorems.Thm_PctDistortion_lemma_10
-- name    : PctDistortion.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:42:06.125198+00:00
-- url     : https://prove2.me/theorems/300d7edc-3d16-44a8-89e4-b4aa2dfc58aa
-- title:
--   Lemma 10 — no arc $(j,i)$ implies $\mathrm{cost}^\alpha_d(i)\le 3\,\mathrm{cost}^\alpha_d(j)$
-- statement:
--   Let $\alpha\in[1/2,1)$, let $\mathcal E=(V,C,\vec\succ)$ be an election and $d\sim\vec\succ$ a consistent metric. If $(j,i)$ is not an arc of the α-majority digraph $G^\alpha_{\mathcal E}$, then
--   $$\mathrm{cost}^\alpha_d(i)\le 3\cdot\mathrm{cost}^\alpha_d(j).$$
--   It generalizes Theorem 24 of Anshelevich et al. (majority tournaments, median cost) and is the first ingredient of Theorem 1.
--
--   Differences from the source:
--   - encoding: finite elections with n voters and m candidates → finite nonempty voter and candidate types; reason: the percentile cost and the lotteries presuppose n, m ≥ 1; with n = 0 the cost is undefined and with m = 0 there is no lottery
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Lemma 10, App. D.2, p.34

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_PctDistortion_IsMetric
import Definitions.Def_PctDistortion_percentileCost
import Definitions.Def_PctDistortion_alphaMajority

set_option autoImplicit false

namespace PctDistortion

/-- **Lemma 10**. Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Lemma 10, App. D.2, p.34: for all `α ∈ [1/2, 1)` and `d ∼ ≻⃗`, if
`(j, i) ∉ E^α` then `cost^α_d(i) ≤ 3 · cost^α_d(j)`. -/
theorem lemma_10 (α : ℝ) (hα₁ : 1 / 2 ≤ α) (hα₂ : α < 1) {V C : Type} [Fintype V] [Nonempty V]
    [Fintype C] [Nonempty C] (E : Election V C) (d : V → C → ℝ) (hd : IsMetric d)
    (hcons : Consistent E d) (i j : C) (hji : ¬ (alphaMajority α E).Adj j i) :
    percentileCost α d i ≤ 3 * percentileCost α d j := by sorry

end PctDistortion
