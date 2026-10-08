-- Prove2me | Theorems.Thm_RobustPower_StochGap_lemma_2_2_smallest_hypercube
-- name    : RobustPower.StochGap.lemma_2_2_smallest_hypercube
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:14:29.368646+00:00
-- url     : https://prove2.me/theorems/7d3e3e25-273b-4c28-8bac-7bf0cd09de9d
-- title:
--   Lemma 2.2 — the bounding box is the smallest hypercube containing a symmetric set
-- statement:
--   Let $S\subseteq\mathbb R^n$ be a bounded symmetric set, and let $H=\{x : x^l_j\le x_j\le x^h_j\}$ be its bounding box, where $x^h_j=\sup_{x\in S}x_j$ and $x^l_j=\inf_{x\in S}x_j$ (displays (2.5)–(2.7)). Then $H$ is a hypercube, $S\subseteq H$, and for every hypercube $H'\subseteq\mathbb R^n$,
--   $$S\subseteq H'\ \Longrightarrow\ H\subseteq H'.$$
--   Thus $H$ is the smallest hypercube containing $S$.
--
--   This is the first step towards locating the point of symmetry of $S$ (Lemma 2.3).
--
--   **Formalization Note** Boundedness of $S$ is implicit on the page, where $x^h_j$ and $x^l_j$ are maxima and minima; the statement uses suprema and infima, so it also covers sets whose extreme coordinates are not attained.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 12, Lemma 2.2 with (2.5)–(2.7)

import Mathlib
import Definitions.Def_RobustPower_StochGap_SymmetricSets

namespace RobustPower.StochGap

/-- Lemma 2.2 (p. 12): for a bounded symmetric set `S ⊆ ℝⁿ`, the box `H` of (2.5)–(2.7) is a
hypercube containing `S`, and it is contained in every hypercube `H'` containing `S`. -/
theorem lemma_2_2_smallest_hypercube {n : ℕ} (S : Set (Fin n → ℝ))
    (hS : IsSymmetric S) (hbdd : Bornology.IsBounded S) :
    IsHypercube (boundingBox S) ∧ S ⊆ boundingBox S ∧
      ∀ H' : Set (Fin n → ℝ), IsHypercube H' → S ⊆ H' → boundingBox S ⊆ H' := by sorry

end RobustPower.StochGap
