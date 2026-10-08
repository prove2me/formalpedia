-- Prove2me | Theorems.Thm_RobustPower_AdaptGap_lemma_2_3_center
-- name    : RobustPower.AdaptGap.lemma_2_3_center
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:41:03.252013+00:00
-- url     : https://prove2.me/theorems/ba5fa2bd-725c-4e74-bc25-6ddfbfa828a8
-- title:
--   Lemma 2.3 — the bounding-hypercube center is the symmetry point
-- statement:
--   Let $S\subseteq\mathbb R^n$ be a bounded set, symmetric about $u\in S$, and let $x^l_j=\inf_{x\in S}x_j$ and $x^h_j=\sup_{x\in S}x_j$ be its coordinatewise infimum and supremum. Then the center of its bounding hypercube is the point of symmetry, and if moreover $S\subseteq\mathbb R^n_+$, every $x\in S$ is at most twice that center, coordinatewise:
--
--   $$x^0:=\frac{x^l+x^h}{2}=u,\qquad S\subseteq\mathbb R^n_+\ \Longrightarrow\ x\le2x^0\quad(x\in S).$$
--
--   This geometric statement identifies a scenario at the center of a symmetric uncertainty set and bounds every scenario by a multiple of it.
--
--   **Formalization Note** Boundedness is implicit on the page, where (2.5)–(2.6) are maxima and minima. The page states $x\le2x^0$ without $S\subseteq\mathbb R^n_+$, but the claim fails without it ($S=[-1,1]$, $x^0=0$, $x=1$); in the paper $S$ is always a nonnegative uncertainty set, so that clause carries the hypothesis.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 12, Lemma 2.3

import Mathlib
import Definitions.Def_RobustPower_AdaptGap_SymmetricSets

namespace RobustPower.AdaptGap

/-- Lemma 2.3, p. 12: for a bounded set `S` symmetric about `u` (boundedness is implicit on the
page in the maxima and minima (2.5)–(2.6)), the centre of the bounding hypercube (2.7) is `u`.
If moreover `S ⊆ ℝⁿ₊` (the paper's setting, used by its proof; the printed second claim fails
for `S = [-1, 1]`), then `x ≤ 2 · x⁰` for all `x ∈ S`. -/
theorem lemma_2_3_center {ι : Type*} [Fintype ι] (S : Set (ι → ℝ))
    (u : ι → ℝ) (hsym : RobustPower.StochGap.IsSymmetricAbout S u)
    (hbdd : Bornology.IsBounded S) :
    boxCenter S = u ∧
      ((∀ x ∈ S, 0 ≤ x) → ∀ x ∈ S, x ≤ (2 : ℝ) • boxCenter S) := by sorry

end RobustPower.AdaptGap
