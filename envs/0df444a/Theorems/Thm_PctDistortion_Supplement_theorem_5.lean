-- Prove2me | Theorems.Thm_PctDistortion_Supplement_theorem_5
-- name    : PctDistortion.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:30:58.791848+00:00
-- url     : https://prove2.me/theorems/9070b309-10aa-4aa9-94a5-aeb8e0de6b90
-- title:
--   Theorem 5 — distortion bounds $3+2f(\lfloor 1/(1-\alpha)\rfloor+1)$ from approximate Caccetta–Häggkvist degree bounds
-- statement:
--   Let $f:\mathbb Z_{\ge3}\to\mathbb R_{\ge0}$ be non-increasing. Suppose there is a constant $\gamma\in\mathbb R$ such that every oriented digraph $G=(V,E)$ with minimum in-degree $\delta^-(G)>0$ and finite girth $g$ satisfies
--   $$\delta^-(G)\le |V|\cdot f(g)+\gamma.$$
--   Then for every election $\mathcal E$, every $\alpha\in[1/2,1)$ and every lottery $p\in\mathrm{ABC}^\alpha(\mathcal E)$, the α-percentile distortion of $p$ is at most
--   $$3+2f\big(\lfloor 1/(1-\alpha)\rfloor+1\big).$$
--
--   So any approximate form of the Caccetta–Häggkvist conjecture translates into an upper bound on the distortion of ABCα-Maximal Lotteries; Theorem 6 is the instance $f(g)=3/(2g)$ given by Theorem 4.
--
--   Differences from the source:
--   - encoding: f : ℤ≥3 → ℝ≥0 non-increasing → f : ℕ → ℝ, assumed nonnegative and non-increasing only on arguments ≥ 3; reason: values below 3 never occur: oriented digraphs have girth ≥ 3 and ⌊1/(1−α)⌋ + 1 ≥ 3 for α ≥ 1/2; no condition is placed on them
--   - encoding: distortion as a supremum of real ratios → the published ℝ≥0∞-valued distortion, bound written as ENNReal.ofReal; reason: ℝ≥0∞ ratio with x/0 = ⊤ (x > 0), 0/0 = 0; distortion ≤ B iff the cost inequality holds for every consistent metric, as in the paper
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Theorem 5, p.21

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_PctDistortion_distortion
import Definitions.Def_PctDistortion_inDeg
import Definitions.Def_PctDistortion_abcMaximal
import Definitions.Def_PctDistortion_Supplement_IsGirth

set_option autoImplicit false

namespace PctDistortion.Supplement

open PctDistortion

/-- **Theorem 5** (Distortion bounds from degree bounds). Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Theorem 5, p.21: "Let
f : Z≥3 → R≥0 be non-increasing. Suppose that there is a constant γ ∈ R such that every oriented
digraph G = (V, E) with minimum in-degree δ−(G) > 0 and finite girth g satisfies
δ−(G) ≤ |V| · f(g) + γ. Then, for every election E, every α ∈ [1/2, 1), and every lottery
p ∈ ABCα(E), the expected α-percentile distortion of p is at most 3 + 2f(⌊1/(1 − α)⌋ + 1)."

**Formalization Note.** `f` is a function `ℕ → ℝ` of which only the values on `g ≥ 3` matter:
it is assumed nonnegative and non-increasing there only. An oriented digraph has girth at least
`3`, so the degree hypothesis only evaluates `f` on `ℤ≥3`, and so does the conclusion
(`⌊1/(1−α)⌋ + 1 ≥ 3` for `α ≥ 1/2`). The constant `γ` is one real number for all digraphs.
Digraphs range over all finite node types; distortion is the published `ℝ≥0∞`-valued
`distortion`. -/
theorem theorem_5 (f : ℕ → ℝ) (hf_nonneg : ∀ g : ℕ, 3 ≤ g → 0 ≤ f g)
    (hf_anti : ∀ g h : ℕ, 3 ≤ g → g ≤ h → f h ≤ f g)
    (hdeg : ∃ γ : ℝ, ∀ (W : Type) [Fintype W] (G : Digraph W) (g : ℕ),
      IsOriented G → 0 < minInDeg G → IsGirth G g →
        (minInDeg G : ℝ) ≤ (Fintype.card W : ℝ) * f g + γ) :
    ∀ (V C : Type) [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C)
      (α : ℝ), 1 / 2 ≤ α → α < 1 → ∀ p ∈ abcAlphaMaximal α E,
        distortion α E p ≤ ENNReal.ofReal (3 + 2 * f (⌊1 / (1 - α)⌋₊ + 1)) := by sorry

end PctDistortion.Supplement
