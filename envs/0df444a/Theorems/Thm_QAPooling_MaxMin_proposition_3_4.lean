-- Prove2me | Theorems.Thm_QAPooling_MaxMin_proposition_3_4
-- name    : QAPooling.MaxMin.proposition_3_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:38:30.428861+00:00
-- url     : https://prove2.me/theorems/15755331-5021-4fc1-bcee-1dfd1b1d07fe
-- title:
--   Proposition 3.4, p. 11, first bullet, for G the expected reward of a proper scoring rule and q ∈ D — Bregman divergence is non-negative
-- statement:
--   Let $s$ be a regular proper scoring rule with expected reward function $G$, forecast domain $\mathcal D$ and exposure function $g$, and write $D_G(x\,\|\,q)=G(x)-G(q)-\langle g(q),x-q\rangle$ for the Bregman divergence. For every $q\in\mathcal D$ and every $x\in\Delta^n$,
--   $$D_G(x\,\|\,q)\ \ge\ 0,$$
--   with equality only when $x=q$.
--
--   By Remark 3.3 of the paper, $D_G(x\,\|\,q)$ is the expected reward an expert with belief $x$ loses by reporting $q$. Non-negativity and strict positivity off the diagonal are what make the agent's worst-case profit in Theorem 4.1 non-negative, and positive unless all experts with positive weight agree.
--
--   **Formalization Note** The paper states this for a general differentiable strictly convex $G$; here $G$ is the expected reward of a proper scoring rule and an exposure function plays the role of the gradient, with the second argument $q$ in $\mathcal D$ (where $g(q)$ is a finite subgradient). The second bullet of Proposition 3.4 (strict convexity of $D_G(\cdot\,\|\,q)$) is not formalized.
-- source:
--   Neyman & Roughgarden, From Proper Scoring Rules to Max-Min Optimal Forecast Aggregation, arXiv:2102.07081v2, p. 11, Proposition 3.4 (first bullet), Definition 3.2

import Mathlib
import Definitions.Def_QAPooling_MaxMin_Model

namespace QAPooling.MaxMin

/-- Proposition 3.4, first bullet (p. 11), for `G` the expected reward of a regular proper scoring
rule and `g` an exposure function: for `q ∈ D` and `x ∈ Δⁿ`, `D_G(x ∥ q) ≥ 0`, with equality only
when `x = q`. -/
theorem proposition_3_4 {n : ℕ} (s : ScoringRule n) (g : (Fin n → ℝ) → Fin n → ℝ)
    (hreg : IsRegular s) (hprop : IsProper s) (hg : IsExposure s g)
    (q : Fin n → ℝ) (hq : q ∈ forecastDomain s) (x : Fin n → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n)) :
    0 ≤ bregman s g x q ∧ (bregman s g x q = 0 → x = q) := by sorry

end QAPooling.MaxMin
