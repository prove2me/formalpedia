-- Prove2me | Theorems.Thm_PctDistortion_Supplement_theorem_6
-- name    : PctDistortion.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:31:39.531631+00:00
-- url     : https://prove2.me/theorems/7cdb6f69-1f7a-45df-9636-3d2321211682
-- title:
--   Theorem 6 — every ABCα-maximal lottery has distortion $\le 3+3/(\lfloor 1/(1-\alpha)\rfloor+1)\le 6-3\alpha$
-- statement:
--   For every election $\mathcal E$, every $\alpha\in[1/2,1)$ and every lottery $p\in\mathrm{ABC}^\alpha(\mathcal E)$, the α-percentile distortion of $p$ is at most
--   $$3+\frac{3}{\lfloor 1/(1-\alpha)\rfloor+1}\;\le\;6-3\alpha.$$
--
--   Both parts are stated: the distortion bound, and the real inequality between the two expressions. Together with the bound $4-1/m$ of Corollary 3 this gives the unconditional upper bound $\min\{4,6-3\alpha\}$ on optimal randomized α-percentile distortion.
--
--   Differences from the source:
--   - encoding: distortion as a supremum of real ratios → the published ℝ≥0∞-valued distortion, bound written as ENNReal.ofReal; reason: ℝ≥0∞ ratio with x/0 = ⊤ (x > 0), 0/0 = 0; distortion ≤ B iff the cost inequality holds for every consistent metric, as in the paper
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Theorem 6, p.22 (= Theorem D, p.5)

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_PctDistortion_distortion
import Definitions.Def_PctDistortion_abcMaximal

set_option autoImplicit false

namespace PctDistortion.Supplement

open PctDistortion

/-- **Theorem 6** (unconditional bound). Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Theorem 6, p.22 (= Theorem D, p.5): "For every
election E, every α ∈ [1/2, 1), and every lottery p ∈ ABCα(E), the α-percentile distortion of p
is at most 3 + 3/(⌊1/(1 − α)⌋ + 1) ≤ 6 − 3α."

Both parts are stated: the distortion bound `3 + 3/(⌊1/(1−α)⌋ + 1)` for every ABCα-maximal
lottery, and the real inequality `3 + 3/(⌊1/(1−α)⌋ + 1) ≤ 6 − 3α`.

**Formalization Note.** Distortion is the published `ℝ≥0∞`-valued `distortion`; elections have
finite nonempty voter and candidate types; `⌊·⌋` is `Nat.floor`. -/
theorem theorem_6 (α : ℝ) (hα₁ : 1 / 2 ≤ α) (hα₂ : α < 1) :
    (∀ (V C : Type) [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C),
      ∀ p ∈ abcAlphaMaximal α E,
        distortion α E p ≤ ENNReal.ofReal (3 + 3 / ((⌊1 / (1 - α)⌋₊ : ℝ) + 1))) ∧
    3 + 3 / ((⌊1 / (1 - α)⌋₊ : ℝ) + 1) ≤ 6 - 3 * α := by sorry

end PctDistortion.Supplement
