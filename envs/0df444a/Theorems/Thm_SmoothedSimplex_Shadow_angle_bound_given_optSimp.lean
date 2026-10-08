-- Prove2me | Theorems.Thm_SmoothedSimplex_Shadow_angle_bound_given_optSimp
-- name    : SmoothedSimplex.Shadow.angle_bound_given_optSimp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T13:18:57.644814+00:00
-- url     : https://prove2.me/theorems/aadc07d1-a344-448f-a12f-42923c6344f5
-- title:
--   Lemma 4.0.11 — angle bound given optSimp (15)
-- statement:
--   Let $n>d\ge3$, let $q$ be a unit vector, and let $a_1,\dots,a_n$ be independent Gaussian random vectors in $\mathbb R^d$ of standard deviation $\sigma$ with $0<\sigma\le1/(3\sqrt{d\ln n})$, centered at points of norm at most $1$. Then
--
--   $$
--   \Pr_{P^1_{1,\dots,d}}\Big[\mathrm{ang}\big(q,\triangle(a_2,\dots,a_d)\big)<\varepsilon\ \Big|\ \mathrm{optSimp}_q(a_1,\dots,a_n)=\{\{1,\dots,d\}\}\Big]\le\frac{9{,}371{,}990\,nd^2\varepsilon}{\sigma^6}. \tag{15}
--   $$
--
--   Given that $\{1,\dots,d\}$ is the optimal facet for the direction $q$, the ray through $q$ is unlikely to pass within angle $\varepsilon$ of the face $\triangle(a_2,\dots,a_d)$ of that facet. Summing over facets and faces gives Lemma 4.0.7.
--
--   **Formalization Note** Indices are 0-based: $\{1,\dots,d\}$ is $I_0=\{i: i<d\}$ and $a_1$ is index $0$. The conditional probability on $P^1_{1,\dots,d}$ given $\mathrm{optSimp}_q=\{I_0\}$ is cross-multiplied: $\Pr[P\cap C\cap E]\le\text{bound}\cdot\Pr[P\cap C]$. Added hypotheses: $\|q\|=1$ ($q$ is the unit vector of Lemma 4.0.7, and condition 1 of $P^1_{1,\dots,d}$ depends on the scale of $q$) and $d\ge3$, $n>d$ (standing assumptions of Section 4).
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Lemma 4.0.11, eq. (15), printed p. 43 (PDF p. 43)

import Mathlib
import Definitions.Def_SmoothedSimplex_Shadow_gaussian
import Definitions.Def_SmoothedSimplex_Shadow_optSimp
import Definitions.Def_SmoothedSimplex_Shadow_ang
import Definitions.Def_SmoothedSimplex_Shadow_setPjI

namespace SmoothedSimplex.Shadow

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

/-- **Lemma 4.0.11 (Angle bound given optSimp)** (Spielman & Teng, arXiv:cs/0111050v7,
Lemma 4.0.11, printed p. 43, PDF p. 43). Let `µ₁, …, µₙ` be Gaussian measures in `ℝ^d` of standard
deviation `σ ≤ 1/(3√(d ln n))` centered at points of norm at most 1. Then
`Pr_{P^1_{1,…,d}}[ang(q, △(a₂, …, a_d)) < ε | optSimp_q(a₁, …, aₙ) = {1, …, d}] ≤ 9,371,990 nd²ε/σ⁶`
(15), where `a₁, …, aₙ` have density `∏ᵢ µᵢ(aᵢ)`.

**Formalization Note.**
* Indices are 0-based: `{1, …, d}` is `I₀ = {i : i < d}` and the paper's `j = 1` is `0 : Fin n`;
  `△(a₂, …, a_d)` is `convexHull (a '' (I₀ \ {0}))`. "`optSimp_q(a) = {1, …, d}`" is
  `optSimp q a = {I₀}` (the set of index sets is the singleton `{I₀}`).
* The conditional probability on `P^1_{1..d}` given `optSimp_q = {I₀}` is cross-multiplied:
  `µ(P ∩ C ∩ E) ≤ bound · µ(P ∩ C)`, with `µ = ∏ gaussian (āᵢ) σ` (no `0/0`).
* **Added hypotheses**: `‖q‖ = 1` (`q` is the unit vector of Lemma 4.0.7; `P^1_{1..d}`'s condition (1)
  is scale-dependent) and `d ≥ 3`, `n > d` (§4's standing assumptions, so `ln n > 0`). `σ > 0`.
* `ang` takes values in `[0, ∞]`; `ε` is any real. -/
theorem angle_bound_given_optSimp {d n : ℕ} [NeZero n] (hd : 3 ≤ d) (hn : d < n)
    (q : EuclideanSpace ℝ (Fin d)) (hq : ‖q‖ = 1)
    (σ : ℝ) (hσ : 0 < σ) (hσ' : σ ≤ 1 / (3 * Real.sqrt ((d : ℝ) * Real.log n)))
    (abar : Fin n → EuclideanSpace ℝ (Fin d)) (habar : ∀ i, ‖abar i‖ ≤ 1) (ε : ℝ) :
    let I₀ : Finset (Fin n) := Finset.univ.filter (fun i => i.val < d)
    let μ : Measure (Fin n → EuclideanSpace ℝ (Fin d)) := Measure.pi (fun i => gaussian (abar i) σ)
    μ (setPjI I₀ 0 ∩ {a | optSimp q a = {I₀}} ∩
        {a | ang q (convexHull ℝ (a '' ((I₀.erase 0 : Finset (Fin n)) : Set (Fin n)))) <
          ENNReal.ofReal ε}) ≤
      ENNReal.ofReal (9371990 * n * d ^ 2 * ε / σ ^ 6) *
        μ (setPjI I₀ 0 ∩ {a | optSimp q a = {I₀}}) := by sorry

end SmoothedSimplex.Shadow
