-- Prove2me | Theorems.Thm_RAREPricing_Existence_lemma_2
-- name    : RAREPricing.Existence.lemma_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:25:47.308243+00:00
-- url     : https://prove2.me/theorems/bc4c095e-168d-4e76-9045-2dd07698a58e
-- title:
--   Lemma 2 — non-negative gains for all on the upper faces of a box
-- statement:
--   Let $J\ne\emptyset$ be a finite set and $\ell_j<h_j$ for $j\in J$. Let
--   $$U=\Big\{x\in\prod_{j\in J}[\ell_j,h_j]:\ x_i=h_i\text{ for some }i\in J\Big\}$$
--   be the union of the upper faces of the box. For each $j\in J$ let $g_j:U\to\mathbb R$ be continuous, and suppose that for all $x\in U$: $\sum_{j\in J}g_j(x)\ge0$, and $x_j=\ell_j\Rightarrow g_j(x)\le0$ for every $j$. Then some $x^*\in U$ has $g_j(x^*)\ge0$ for all $j\in J$.
--
--   This "inner KKM" is used twice: with market-share gains (Lemma 3) and with revenue gains of responders against a large deviation (Lemma 7).
--
--   **Formalization Note.** $J$ is a nonempty finite type `ι`; each $g_j$ is a function on `ι → ℝ` that is `ContinuousOn` $U$ (its values off $U$ are irrelevant).
--
--   Differences from the source:
--   - encoding: $g_j:U\to\mathbb R$ continuous → `g j : (ι → ℝ) → ℝ` with `ContinuousOn (g j) U`; reason: any function on $U$ extends to $\mathbb R^J$ and only its values on $U$ enter the statement.
-- source:
--   Chaudhury, Garg, Huang, Sharma, RARE: Response-Aware Rational Equilibrium in Budget-Constrained Pricing Games, STOC 2027 submission (manuscript sha256 e9bb863f…), pp. 17–18 (PDF 19–20), Lemma 2

import Mathlib
import Definitions.Def_RAREPricing_Existence_Model

namespace RAREPricing.Existence

theorem lemma_2 {ι : Type*} [Fintype ι] [Nonempty ι] (ℓ h : ι → ℝ) (hℓh : ∀ j, ℓ j < h j)
    (g : ι → (ι → ℝ) → ℝ) (hg_cont : ∀ j, ContinuousOn (g j) (upperFaces ℓ h))
    (h_total : ∀ x ∈ upperFaces ℓ h, 0 ≤ ∑ j, g j x)
    (h_low : ∀ x ∈ upperFaces ℓ h, ∀ j, x j = ℓ j → g j x ≤ 0) :
    ∃ x ∈ upperFaces ℓ h, ∀ j, 0 ≤ g j x := by sorry

end RAREPricing.Existence
