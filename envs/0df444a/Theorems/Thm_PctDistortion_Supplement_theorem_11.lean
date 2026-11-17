-- Prove2me | Theorems.Thm_PctDistortion_Supplement_theorem_11
-- name    : PctDistortion.Supplement.theorem_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:33:41.781823+00:00
-- url     : https://prove2.me/theorems/43a87ef3-4bc1-45d5-9721-86f62283a7de
-- title:
--   Theorem 11 — C1-Maximal Lotteries has α-percentile distortion at most $4$
-- statement:
--   For every $\alpha\in[1/2,1)$, C1-Maximal Lotteries has α-percentile distortion at most $4$.
--
--   Precisely: let $\mathcal E$ be an election, $T$ a majority tournament of $\mathcal E$ (every arc supported by at least $n/2$ voters, pairwise ties oriented arbitrarily), and $a\in\Delta\mathcal C$ a lottery such that $(a,a)$ is a Nash equilibrium of the Condorcet game $\mathcal G^C_T$. Then
--   $$\mathrm{dist}^\alpha_{\mathcal E}(a)\le 4.$$
--
--   With the lower bound $4-3/m$ for unweighted tournament rules (Corollary 5), this shows the bound $4$ is asymptotically tight.
--
--   Differences from the source:
--   - encoding: the lottery returned by C1-Maximal Lotteries on the majority tournament T (the a with (a, a) the unique equilibrium) → every a with (a, a) a Nash equilibrium of the Condorcet game, for every majority tournament T of E; reason: by Laslier's Proposition 6 (cited) the symmetric equilibrium is unique, so this is the same lottery; quantifying over every tie orientation covers the arbitrary orientation of the paper
--   - encoding: distortion as a supremum of real ratios → the published ℝ≥0∞-valued distortion, bound written as ENNReal.ofReal; reason: ℝ≥0∞ ratio with x/0 = ⊤ (x > 0), 0/0 = 0; distortion ≤ B iff the cost inequality holds for every consistent metric, as in the paper
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Theorem 11, p.30 (App. B.1), with Definitions 8–9, p.30

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_PctDistortion_distortion
import Definitions.Def_PctDistortion_Supplement_c1Maximal

set_option autoImplicit false

namespace PctDistortion.Supplement

open PctDistortion

/-- **Theorem 11** (C1-Maximal Lotteries). Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Theorem 11, p.30 (App. B.1): "For every
α ∈ [1/2, 1), C1-Maximal Lotteries has α-percentile distortion at most 4."

C1-Maximal Lotteries returns, on an election `E`, the lottery `a` for which `(a, a)` is the
equilibrium of the Condorcet game on `E`'s majority tournament `T` (pairwise ties oriented
arbitrarily). The bound is stated for every majority tournament `T` of `E` and every such `a`.

**Formalization Note.** `T` is any `IsMajorityTournament E T` (each arc supported by at least
`n/2` voters, ties oriented arbitrarily); it is not the published `alphaMajority (1/2) E`, which
has no arc between tied candidates. The existence and uniqueness of the equilibrium (Laslier,
Proposition 6, cited) are not assumed: the bound holds for every `a ∈ c1Maximal T`. -/
theorem theorem_11 (α : ℝ) (hα₁ : 1 / 2 ≤ α) (hα₂ : α < 1) {V C : Type} [Fintype V]
    [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C) (T : Digraph C)
    (hT : IsMajorityTournament E T) (a : C → ℝ) (ha : a ∈ c1Maximal T) :
    distortion α E a ≤ 4 := by sorry

end PctDistortion.Supplement
