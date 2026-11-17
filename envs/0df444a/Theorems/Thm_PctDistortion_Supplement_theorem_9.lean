-- Prove2me | Theorems.Thm_PctDistortion_Supplement_theorem_9
-- name    : PctDistortion.Supplement.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:33:13.676388+00:00
-- url     : https://prove2.me/theorems/37ba999c-d19e-425f-a767-7b8193557ed6
-- title:
--   Theorem 9 — the uniform lottery on Pareto undominated candidates has max-cost distortion $\le 3-2/m$
-- statement:
--   Let $\mathcal E$ be an election with $n$ voters and $m$ candidates, and let $P$ be its set of Pareto undominated candidates. For every $\alpha\in[1-1/n,1)$, choosing uniformly from $P$ has α-percentile distortion at most
--   $$3-\frac2m.$$
--
--   For $\alpha\ge 1-1/n$ the α-percentile cost is the cost of the worst-off voter (max cost), and this bound matches the lower bound for all randomized voting rules (Corollary 4).
--
--   Differences from the source:
--   - encoding: choosing uniformly from P, n voters, m candidates → the lottery paretoUniform E; n = Fintype.card V, m = Fintype.card C; reason: direct transcription; the hypothesis is exactly 1 − 1/n ≤ α < 1 with no separate α ≥ 1/2
--   - encoding: distortion as a supremum of real ratios → the published ℝ≥0∞-valued distortion, bound written as ENNReal.ofReal; reason: ℝ≥0∞ ratio with x/0 = ⊤ (x > 0), 0/0 = 0; distortion ≤ B iff the cost inequality holds for every consistent metric, as in the paper
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Theorem 9, p.29 (App. A)

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_PctDistortion_distortion
import Definitions.Def_PctDistortion_Supplement_paretoUniform

set_option autoImplicit false

namespace PctDistortion.Supplement

open PctDistortion

/-- **Theorem 9** (max cost). Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Theorem 9, p.29 (App. A): "Choosing uniformly from the Pareto
undominated candidates P has α-percentile distortion at most 3 − 2/m for all α ∈ [1 − 1/n, 1)."

Here `n` is the number of voters and `m` the number of candidates.

**Formalization Note.** The rule is `paretoUniform E`, the uniform lottery on
`P(E) = {a | ∀ b ≠ a, ∃ v, a ≻_v b}`. The range of `α` is exactly `[1 − 1/n, 1)`, with no
separate `α ≥ 1/2` (for `n ≥ 2` it follows; for `n = 1` it is not assumed). Distortion is the
published `ℝ≥0∞`-valued `distortion`. -/
theorem theorem_9 {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C]
    (E : Election V C) (α : ℝ) (hα₁ : 1 - 1 / (Fintype.card V : ℝ) ≤ α) (hα₂ : α < 1) :
    distortion α E (paretoUniform E) ≤
      ENNReal.ofReal (3 - 2 / (Fintype.card C : ℝ)) := by sorry

end PctDistortion.Supplement
