-- Prove2me | Theorems.Thm_StackingStars_Main_lemma_9
-- name    : StackingStars.Main.lemma_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:42:59.499357+00:00
-- url     : https://prove2.me/theorems/9ad10733-2389-42b0-994c-cd1e2d91d915
-- title:
--   Lemma 9 — a vertical parallelogram of at most twice the area
-- statement:
--   A vertical parallelogram is a parallelogram with two vertical sides, $T=\{(x,y): x_0\le x\le x_1,\ sx+b_0\le y\le sx+b_1\}$. For every compact convex set $C\subseteq\mathbb R^2$ of positive area there is a vertical parallelogram $T\supseteq C$ with
--   $$|T|\le 2|C| .$$
--   The lemma is used in the proof of Theorem 10 to replace the convex container by a parallelogram.
--
--   Differences from the source:
--   - encoding: a vertical parallelogram T → vertParallelogram x₀ x₁ s b₀ b₁ = {x₀ ≤ x ≤ x₁, s x + b₀ ≤ y ≤ s x + b₁}; reason: every parallelogram with two vertical sides has this form
-- source:
--   Abrahamsen, Conradi, Khan, Stade, Wong, Yan, Zhang, Stacking Stars: Minimum-Area Packing with and without Rotation, STOC 2027 submission (manuscript sha256 ee9554eb…), p. 13, Lemma 9

import Mathlib
import Definitions.Def_StackingStars_Main_Geometry

namespace StackingStars.Main

/-- Abrahamsen et al., *Stacking Stars*, STOC 2027 submission (manuscript sha256 ee9554eb…),
p. 13 (PDF 15), Lemma 9: "Every compact convex set C of positive area is contained in a vertical
parallelogram (that is, a parallelogram with two vertical sides) T with |T| ≤ 2|C|." -/
theorem lemma_9 (C : Set Pt) (hC : IsCompact C) (hconv : Convex ℝ C)
    (hpos : 0 < MeasureTheory.volume C) :
    ∃ x₀ x₁ s b₀ b₁ : ℝ, C ⊆ vertParallelogram x₀ x₁ s b₀ b₁ ∧
      area (vertParallelogram x₀ x₁ s b₀ b₁) ≤ 2 * area C := by sorry

end StackingStars.Main
