-- Prove2me | Theorems.Thm_RobustPower_StochGap_lemma_2_3_center_is_symmetry_point
-- name    : RobustPower.StochGap.lemma_2_3_center_is_symmetry_point
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:14:55.123797+00:00
-- url     : https://prove2.me/theorems/2658cc63-9f5d-4953-bf68-dfaa30fab72b
-- title:
--   Lemma 2.3 — the centre of the bounding hypercube is the point of symmetry
-- statement:
--   Let $S\subseteq\mathbb R^n$ be a bounded symmetric set with bounding box given by $x^l_j=\inf_{x\in S}x_j$, $x^h_j=\sup_{x\in S}x_j$, and let $x^0$ be its centre,
--   $$x^0_j=\frac{x^l_j+x^h_j}{2},\qquad j=1,\dots,n.$$
--   Then:
--   1. $S$ is symmetric about $x^0$;
--   2. $x^0$ is the only point of symmetry of $S$;
--   3. if moreover $S\subseteq\mathbb R^n_+$, then $x\le 2x^0$ for every $x\in S$.
--
--   The third claim is what makes a doubled solution for the central scenario feasible for every scenario in the proof of Theorem 2.1.
--
--   **Formalization Note** The page states $x\le 2x^0$ without the hypothesis $S\subseteq\mathbb R^n_+$, but its proof uses $x^l_j\ge0$ and the claim fails without it ($S=[-1,1]$, $x^0=0$, $x=1$); in the paper $S$ is always an uncertainty set in $\mathbb R^m_+$. Boundedness, implicit on the page in the maxima and minima of (2.5)–(2.6), is assumed explicitly; without it the point of symmetry need not be unique.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 12, Lemma 2.3

import Mathlib
import Definitions.Def_RobustPower_StochGap_SymmetricSets

namespace RobustPower.StochGap

/-- Lemma 2.3 (p. 12): for a bounded symmetric set `S ⊆ ℝⁿ`, the centre
`x⁰ = (xˡ + xʰ)/2` of the box (2.7) is a point of symmetry of `S`, and it is the only one.
If moreover `S ⊆ ℝⁿ₊` (the paper's setting, needed by its proof), then `x ≤ 2 x⁰` for all
`x ∈ S`. -/
theorem lemma_2_3_center_is_symmetry_point {n : ℕ} (S : Set (Fin n → ℝ))
    (hS : IsSymmetric S) (hbdd : Bornology.IsBounded S) :
    IsSymmetricAbout S ((1 / 2 : ℝ) • (xl S + xh S)) ∧
      (∀ u : Fin n → ℝ, IsSymmetricAbout S u → u = (1 / 2 : ℝ) • (xl S + xh S)) ∧
      ((∀ x ∈ S, 0 ≤ x) → ∀ x ∈ S, x ≤ (2 : ℝ) • ((1 / 2 : ℝ) • (xl S + xh S))) := by sorry

end RobustPower.StochGap
