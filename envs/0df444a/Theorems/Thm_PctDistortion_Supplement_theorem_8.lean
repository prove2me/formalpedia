-- Prove2me | Theorems.Thm_PctDistortion_Supplement_theorem_8
-- name    : PctDistortion.Supplement.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:32:47.307283+00:00
-- url     : https://prove2.me/theorems/e23dbac7-b64e-4618-b27a-8f3a39b2ac3d
-- title:
--   Theorem 8 — every weighted tournament rule has α-percentile distortion $\ge 3+2/\lfloor 1/(1-\alpha)\rfloor-\epsilon$
-- statement:
--   For every weighted tournament rule $A$, every $\alpha\in[1/2,1)$ and every $\epsilon>0$, there exists an election $\mathcal E$ such that
--   $$\mathrm{dist}^\alpha_{\mathcal E}(A(\mathcal E))\ \ge\ 3+\frac{2}{\lfloor 1/(1-\alpha)\rfloor}-\epsilon.$$
--
--   The bound matches, asymptotically, the upper bound for ABCα-Maximal Lotteries of Theorem B under the Thomassé–Charbit conjecture, so under that conjecture ABCα-Maximal Lotteries is an optimal weighted tournament rule.
--
--   Differences from the source:
--   - encoding: a weighted tournament rule (receives only the pairwise victory counts) → IsWeightedTournamentRule A: a randomized voting rule whose outputs agree on any two elections over the same candidate type with equal pairwise counts (voter types may differ); reason: a rule that sees only the counts is exactly a function of the count table
--   - encoding: distortion as a supremum of real ratios → the published ℝ≥0∞-valued distortion, bound written as ENNReal.ofReal; reason: ℝ≥0∞ ratio with x/0 = ⊤ (x > 0), 0/0 = 0; distortion ≤ B iff the cost inequality holds for every consistent metric, as in the paper
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Theorem 8, p.23 (proof App. F.2, pp.42–44; = Theorem A, part 2, p.3)

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_PctDistortion_distortion
import Definitions.Def_PctDistortion_Supplement_IsWeightedTournamentRule

set_option autoImplicit false

namespace PctDistortion.Supplement

open PctDistortion

/-- **Theorem 8** (lower bound for weighted tournament rules). Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Theorem 8, p.23 (proof App.
F.2, pp.42–44; = Theorem A, part 2, p.3): "For every weighted tournament rule A, every
α ∈ [1/2, 1), and every ϵ > 0, there exists an election E such that
dist^α_E(A(E)) ≥ 3 + 2/⌊1/(1−α)⌋ − ϵ."

**Formalization Note.** A weighted tournament rule is `IsWeightedTournamentRule`: a randomized
voting rule whose output depends only on the pairwise vote counts (elections on the same candidate
type with equal counts get the same lottery). The election's sizes are not fixed. Distortion is the
published `ℝ≥0∞`-valued `distortion`. -/
theorem theorem_8 (A : VotingRule) (hA : IsWeightedTournamentRule A) (α : ℝ)
    (hα₁ : 1 / 2 ≤ α) (hα₂ : α < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ (V C : Type) (_ : Fintype V) (_ : Nonempty V) (_ : Fintype C) (_ : Nonempty C)
      (E : Election V C),
      ENNReal.ofReal (3 + 2 / (⌊1 / (1 - α)⌋₊ : ℝ) - ε) ≤ distortion α E (A V C E) := by sorry

end PctDistortion.Supplement
