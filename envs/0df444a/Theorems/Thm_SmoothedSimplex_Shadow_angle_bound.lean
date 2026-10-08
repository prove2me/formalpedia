-- Prove2me | Theorems.Thm_SmoothedSimplex_Shadow_angle_bound
-- name    : SmoothedSimplex.Shadow.angle_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T13:19:15.243989+00:00
-- url     : https://prove2.me/theorems/bb8fb7f8-0d96-423e-8d28-d93caa547515
-- title:
--   Lemma 4.0.7 — angle bound: $\Pr_P[\mathrm{ang}_q<\varepsilon]\le 9{,}372{,}424\,nd^3\varepsilon/\sigma^6$
-- statement:
--   Let $d\ge3$ and $n>d$. Let $q$ be any unit vector and let $a_1,\dots,a_n$ be independent Gaussian random vectors in $\mathbb R^d$ of standard deviation $\sigma$ with $0<\sigma\le1/(3\sqrt{d\ln n})$, centered at points of norm at most $1$. Then
--
--   $$
--   \Pr_P\big[\mathrm{ang}_q(a_1,\dots,a_n)<\varepsilon\big]\le\frac{9{,}372{,}424\,nd^3\varepsilon}{\sigma^6},
--   $$
--
--   where $P$ is the event $\{\|a_i\|\le2\ \forall i\}$ and $\Pr_P$ is probability conditioned on $P$.
--
--   If the objective direction turns by less than $\mathrm{ang}_q$, the optimal facet does not change; so this bound controls the probability that the shadow-vertex method pivots in a given small angular step, which is how Theorem 4.0.1 is proved.
--
--   **Formalization Note** The conditional probability is cross-multiplied: $\Pr[P\cap\{\mathrm{ang}_q<\varepsilon\}]\le\text{bound}\cdot\Pr[P]$. $\mathrm{ang}_q$ takes values in $[0,\infty]$ and is $\infty$ when $\mathrm{optSimp}_q=\emptyset$.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Lemma 4.0.7, printed p. 41 (PDF p. 41)

import Mathlib
import Definitions.Def_SmoothedSimplex_Shadow_gaussian
import Definitions.Def_SmoothedSimplex_Shadow_angQ
import Definitions.Def_SmoothedSimplex_Shadow_setP

namespace SmoothedSimplex.Shadow

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

/-- **Lemma 4.0.7 (Angle bound)** (Spielman & Teng, arXiv:cs/0111050v7, Lemma 4.0.7, printed p. 41,
PDF p. 41). Let `d ≥ 3` and `n > d`. Let `q` be any unit vector and let `µ₁, …, µₙ` be Gaussian
measures in `ℝ^d` of standard deviation `σ ≤ 1/(3√(d ln n))` centered at points of norm at most 1.
Then `Pr_P[ang_q(a₁, …, aₙ) < ε] ≤ 9,372,424 nd³ε/σ⁶`, where `a₁, …, aₙ` have density
`∏ᵢ µᵢ(aᵢ)`.

**Formalization Note.** `P = {‖aᵢ‖ ≤ 2 ∀ i}` (Definition 4.0.4); `Pr_P` is the conditional
probability on `P`, cross-multiplied: `µ(P ∩ {ang_q < ε}) ≤ bound · µ(P)`, with
`µ = ∏ gaussian (āᵢ) σ`. `ang_q` (Definition 4.0.3) takes values in `[0, ∞]` and equals `∞` when
`optSimp_q(a) = ∅`. `σ > 0`. -/
theorem angle_bound {d n : ℕ} (hd : 3 ≤ d) (hn : d < n)
    (q : EuclideanSpace ℝ (Fin d)) (hq : ‖q‖ = 1)
    (σ : ℝ) (hσ : 0 < σ) (hσ' : σ ≤ 1 / (3 * Real.sqrt ((d : ℝ) * Real.log n)))
    (abar : Fin n → EuclideanSpace ℝ (Fin d)) (habar : ∀ i, ‖abar i‖ ≤ 1) (ε : ℝ) :
    let μ : Measure (Fin n → EuclideanSpace ℝ (Fin d)) := Measure.pi (fun i => gaussian (abar i) σ)
    μ (setP ∩ {a | angQ q a < ENNReal.ofReal ε}) ≤
      ENNReal.ofReal (9372424 * n * d ^ 3 * ε / σ ^ 6) * μ setP := by sorry

end SmoothedSimplex.Shadow
