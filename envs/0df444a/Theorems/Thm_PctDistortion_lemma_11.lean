-- Prove2me | Theorems.Thm_PctDistortion_lemma_11
-- name    : PctDistortion.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:42:11.160472+00:00
-- url     : https://prove2.me/theorems/e31d7c4b-1197-4e3e-9ef2-70da84e4eb61
-- title:
--   Lemma 11 — uncovered candidates have cost at most $5\,\mathrm{cost}^\alpha_d(j)$
-- statement:
--   Let $\alpha\in[1/2,1)$, let $\mathcal E=(V,C,\vec\succ)$ be an election, $j\in C$, and $d\sim\vec\succ$ a consistent metric. If $i$ lies in the uncovered set $U(G^\alpha_{\mathcal E})$, then
--   $$\mathrm{cost}^\alpha_d(i)\le 5\cdot\mathrm{cost}^\alpha_d(j).$$
--   It generalizes Theorem 27 of Anshelevich et al. and is the second ingredient of Theorem 1.
--
--   Differences from the source:
--   - encoding: finite elections with n voters and m candidates → finite nonempty voter and candidate types; reason: the percentile cost and the lotteries presuppose n, m ≥ 1; with n = 0 the cost is undefined and with m = 0 there is no lottery
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Lemma 11, App. D.2, p.34

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_PctDistortion_IsMetric
import Definitions.Def_PctDistortion_percentileCost
import Definitions.Def_PctDistortion_alphaMajority
import Definitions.Def_PctDistortion_uncovered

set_option autoImplicit false

namespace PctDistortion

/-- **Lemma 11**. Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Lemma 11, App. D.2, p.34: for all `α ∈ [1/2, 1)`, `j ∈ C` and `d ∼ ≻⃗`, if
`i ∈ U(G^α)` then `cost^α_d(i) ≤ 5 · cost^α_d(j)`. -/
theorem lemma_11 (α : ℝ) (hα₁ : 1 / 2 ≤ α) (hα₂ : α < 1) {V C : Type} [Fintype V] [Nonempty V]
    [Fintype C] [Nonempty C] (E : Election V C) (d : V → C → ℝ) (hd : IsMetric d)
    (hcons : Consistent E d) (i j : C) (hi : i ∈ uncovered (alphaMajority α E)) :
    percentileCost α d i ≤ 5 * percentileCost α d j := by sorry

end PctDistortion
