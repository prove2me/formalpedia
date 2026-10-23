-- Prove2me | Theorems.Thm_QAPooling_MaxMin_proposition_3_1
-- name    : QAPooling.MaxMin.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:38:32.059309+00:00
-- url     : https://prove2.me/theorems/b995b6e4-5dc6-4c64-bb12-b38634d2687d
-- title:
--   Proposition 3.1, p. 10, only-if direction on the forecast domain D — Savage representation of a proper scoring rule
-- statement:
--   Let $s$ be a regular proper scoring rule on $n$ outcomes, with expected reward function $G(p)=\sum_j p_j s(p;j)$ and forecast domain $\mathcal D$. Then:
--
--   1. $G$ is convex on $\Delta^n$;
--   2. the map $p\mapsto s(p;\cdot)$ is itself an exposure function of $s$: for all $p\in\mathcal D$ and every outcome $j$,
--   $$s(p;j)=G(p)+\langle s(p;\cdot),\,\delta_j-p\rangle;$$
--   3. for every exposure function $g$ of $s$ and every $q\in\mathcal D$, the vector $g(q)$ is a subgradient of $G$ at $q$ relative to $\Delta^n$:
--   $$G(y)\ \ge\ G(q)+\langle g(q),\,y-q\rangle\qquad\text{for all } y\in\Delta^n.$$
--
--   This is the only-if direction of the Savage representation (Gneiting and Raftery, Theorem 2): a proper scoring rule is the tangent plane of its convex expected reward. Clause 2 shows exposure functions exist, and clause 3 is what makes $G$'s supporting hyperplanes available in the max-min argument.
--
--   **Formalization Note** The statement is restricted to the forecast domain $\mathcal D$, where all scores are finite; the paper's exposure function may take the value $-\infty$ at boundary points outside $\mathcal D$, which are not covered here. Subgradients are relative to $\Delta^n$, the domain of $G$ (footnote 10). The "if" direction is not formalized.
-- source:
--   Neyman & Roughgarden, From Proper Scoring Rules to Max-Min Optimal Forecast Aggregation, arXiv:2102.07081v2, p. 10, Proposition 3.1 (only-if direction, Equation (2)), footnote 10

import Mathlib
import Definitions.Def_QAPooling_MaxMin_Model

namespace QAPooling.MaxMin

/-- Proposition 3.1, only-if direction, on the forecast domain `D` (p. 10). A regular proper scoring
rule has a convex expected reward `G` on `Δⁿ`; `s(p; ·)` itself is an exposure function
(Equation (2) on `D`); and every exposure function `g` gives, at every `q ∈ D`, a subgradient
`g(q)` of `G` relative to `Δⁿ`. -/
theorem proposition_3_1 {n : ℕ} (s : ScoringRule n) (hreg : IsRegular s) (hprop : IsProper s) :
    ConvexOn ℝ (stdSimplex ℝ (Fin n)) (expectedReward s) ∧
      IsExposure s (fun p j => (s p j).toReal) ∧
      ∀ g : (Fin n → ℝ) → Fin n → ℝ, IsExposure s g →
        ∀ q ∈ forecastDomain s, IsSubgradientOn (expectedReward s) (g q) q := by sorry

end QAPooling.MaxMin
