-- Prove2me | Theorems.Thm_PctDistortion_theorem_B
-- name    : PctDistortion.theorem_B
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:43:25.372943+00:00
-- url     : https://prove2.me/theorems/bc16a7f0-2bc2-4418-8adc-d265812f9ceb
-- title:
--   Theorem B — ABCα-Maximal Lotteries has distortion $\le 3+2/\lfloor 1/(1-\alpha)\rfloor$ iff every α-majority digraph has a vertex of in-degree $\le |V|/\lfloor 1/(1-\alpha)\rfloor$
-- statement:
--   Let $\alpha\in[1/2,1)$ and $s=\lfloor1/(1-\alpha)\rfloor$. ABCα-Maximal Lotteries has expected α-percentile distortion at most $3+2/s$ if and only if every α-majority digraph $G=(V,E)$ has a vertex of in-degree at most $|V|/s$. Since the rule returns an arbitrary ABCα-maximal lottery, this is stated as two claims:
--
--   1. every α-majority digraph $G=(V,E)$ has a vertex $w$ with $\deg^-(w)\le|V|/s$ if and only if every election $\mathcal E$ and every $a\in\mathrm{ABC}^\alpha(\mathcal E)$ satisfy $\mathrm{dist}^\alpha_{\mathcal E}(a)\le 3+2/s$;
--   2. if the degree condition fails, there is an election $\mathcal E$ with $\mathrm{ABC}^\alpha(\mathcal E)\ne\emptyset$ such that $\mathrm{dist}^\alpha_{\mathcal E}(a)>3+2/s$ for every $a\in\mathrm{ABC}^\alpha(\mathcal E)$.
--
--   The degree condition with strict inequality is the Thomassé–Charbit conjecture, so the theorem ties the optimal distortion of weighted tournament rules to a twenty-year-old open problem in graph theory. The bound $3+2/s$ matches the lower bound for weighted tournament rules (Theorem A).
--
--   Differences from the source:
--   - reading: "ABCα-Maximal Lotteries has expected α-percentile distortion at most 3 + 2/s if and only if …", the rule returning an arbitrary lottery of ABCα(E) → (TC ↔ every a ∈ ABCα(E) of every E has distortion ≤ 3 + 2/s) ∧ (¬TC → some E with ABCα(E) ≠ ∅ where every a has distortion > 3 + 2/s); reason: the iff then holds for every way of choosing the arbitrary lottery, including the lexicographically first; the proof (Theorems 1 and 2, Proposition 1) gives both clauses
--   - reading: "every α-majority digraph G = (V, E)" → every digraph in M_α, the α-majority digraphs of finite elections with nonempty voter and candidate sets; reason: M_α is defined as the α-majority digraphs of finite elections (Definition 3); arcless digraphs from voterless elections are also realized with two opposite voters
--   - encoding: finite elections with n voters and m candidates → finite nonempty voter and candidate types; reason: the percentile cost and the lotteries presuppose n, m ≥ 1; with n = 0 the cost is undefined and with m = 0 there is no lottery
--   - encoding: ratio cost(p)/min_c cost(c) in the reals → ratio in [0, ∞] with x/0 = ∞ (x > 0) and 0/0 = 0; reason: the ratio is undefined when the optimal cost is 0; this convention makes dist ≤ B equivalent to cost(p) ≤ B·min cost for every consistent metric
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Theorem B, p.4 (proof §5.2, p.18)

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_PctDistortion_distortion
import Definitions.Def_PctDistortion_abcMaximal
import Definitions.Def_PctDistortion_ThomasseCharbitDegree

set_option autoImplicit false

namespace PctDistortion

/-- **Theorem B** (Characterization). Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Theorem B, p.4 (proof §5.2, p.18): ABCα-Maximal Lotteries
has expected α-percentile distortion at most `3 + 2/⌊1/(1−α)⌋` if and only if every α-majority
digraph `G = (V, E)` has a vertex of in-degree at most `|V|/⌊1/(1−α)⌋`.

Write `s = ⌊1/(1−α)⌋` and `B = 3 + 2/s`. For every `α ∈ [1/2, 1)`:
1. the degree condition holds iff every ABCα-maximal lottery of every election has distortion at
   most `B`;
2. if the degree condition fails, some election has a nonempty set of ABCα-maximal lotteries, all
   of distortion strictly more than `B`.

**Formalization Note.** The rule returns an arbitrary element of `ABCα(E)`. Part 1 gives "if" for
every choice; part 2 gives "only if" for every choice, including "lexicographically first", since
it exhibits an election where no choice is within `B`. Distortion is `ℝ≥0∞`-valued; elections have
finite nonempty voter and candidate sets. -/
theorem theorem_B (α : ℝ) (hα₁ : 1 / 2 ≤ α) (hα₂ : α < 1) :
    (ThomasseCharbitDegree α ↔
      ∀ (V C : Type) [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C),
        ∀ a ∈ abcAlphaMaximal α E,
          distortion α E a ≤ ENNReal.ofReal (3 + 2 / (⌊1 / (1 - α)⌋₊ : ℝ))) ∧
    (¬ ThomasseCharbitDegree α →
      ∃ (V C : Type) (_ : Fintype V) (_ : Nonempty V) (_ : Fintype C) (_ : Nonempty C)
        (E : Election V C), (abcAlphaMaximal α E).Nonempty ∧
        ∀ a ∈ abcAlphaMaximal α E,
          ENNReal.ofReal (3 + 2 / (⌊1 / (1 - α)⌋₊ : ℝ)) < distortion α E a) := by sorry

end PctDistortion
