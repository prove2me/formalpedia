-- Prove2me | Theorems.Thm_WassersteinLinOpt_Ball_problem10_attained
-- name    : WassersteinLinOpt.Ball.problem10_attained
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T21:12:01.319996+00:00
-- url     : https://prove2.me/theorems/4a6daf16-c772-43bc-b05a-26907c6a29cc
-- title:
--   Lemma 2 — the discrete relaxation (10) attains its finite value
-- statement:
--   Throughout, $(X,d)$ is a proper metric space (every closed ball is compact; such a space is complete and separable, hence Polish) with its Borel $\sigma$-algebra, and $p \ge 1$, $r > 0$ are real.
--
--   Assume the hypotheses of Theorem 4: $\nu=\sum_{i=1}^N\alpha_i\delta_{y_i}$ with distinct atoms $y_1,\dots,y_N\in X$, weights $\alpha_i\ge0$, $\sum_i\alpha_i=1$; $f:X\to\mathbb R$ is upper semicontinuous and, for every $\mu\in\mathcal B_r(\nu)$, one of $\int[f]_+d\mu$, $\int[-f]_+d\mu$ is finite; and $f(x)\le c[1+d^{p'}(x,x_0)]$ for all $x$, for some $x_0\in X$, $c>0$, $p'\in(0,p)$. Let $Y=\{y_1,\dots,y_N\}$ and consider problem (10):
--
--   $$\text{maximize}_\gamma\ \int_{X\times Y}f(x_1)\,d\gamma(x_1,x_2)\quad\text{s.t.}\quad\gamma\in\mathcal D_{N+1}(X\times Y),\ \gamma(X\times\{y_i\})=\alpha_i\ (i\le N),\ \int_{X\times Y}d^p(x_1,x_2)\,d\gamma\le r^p.$$
--
--   **Lemma 2.** If the optimal value of problem (10) is finite, then it is attained by a feasible $\gamma$.
--
--   **Formalization Note.** The optimal value is the `EReal` supremum of `quasiIntegral (fun z => f z.1) γ` over `problem10Feasible p r y α`; "finite" is `≠ ⊤ ∧ ≠ ⊥`. A finitely supported $\nu$ has a finite $p$-th moment, so that part of the assumptions of Theorem 4 is not stated separately.
-- source:
--   Yue, Kuhn & Wiesemann, On linear optimization over Wasserstein balls, Math. Program. 195 (2022) 1107–1122, https://doi.org/10.1007/s10107-021-01673-8, p. 1118, Lemma 2

import Mathlib
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinBall
import Definitions.Def_WassersteinLinOpt_Ball_quasiIntegral
import Definitions.Def_WassersteinLinOpt_Ball_problem10Feasible

open MeasureTheory
open scoped ENNReal NNReal

namespace WassersteinLinOpt.Ball

/-- Lemma 2, p. 1118. Under the assumptions of Theorem 4 (`ν = ∑ᵢ αᵢ δ_{yᵢ}` on `N` distinct
atoms, `f` upper semicontinuous and quasi-integrable on `𝓑_r(ν)`, and the growth condition
`f(x) ≤ c[1 + d^{p′}(x, x₀)]` with `c > 0`, `p′ ∈ (0, p)`), if the optimal value of problem (10),
`sup{∫ f(x₁) dγ(x₁, x₂) : γ feasible in (10)}`, is finite, then it is attained. -/
theorem problem10_attained {X : Type*} [MetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] (p r : ℝ) (hp : 1 ≤ p) (hr : 0 < r) {N : ℕ}
    (y : Fin N → X) (hy : Function.Injective y) (α : Fin N → ℝ≥0) (hα : ∑ i, α i = 1)
    (ν : ProbabilityMeasure X)
    (hν : (ν : Measure X) = ∑ i, (α i : ℝ≥0∞) • Measure.dirac (y i))
    (f : X → ℝ) (hf : UpperSemicontinuous f)
    (hquasi : ∀ μ ∈ wassersteinBall p r ν,
      ∫⁻ x, ENNReal.ofReal (f x) ∂(μ : Measure X) < ⊤ ∨
        ∫⁻ x, ENNReal.ofReal (-f x) ∂(μ : Measure X) < ⊤)
    (x₀ : X) (c p' : ℝ) (hc : 0 < c) (hp'0 : 0 < p') (hp'p : p' < p)
    (hgrowth : ∀ x : X, f x ≤ c * (1 + dist x x₀ ^ p'))
    (hfin : (⨆ γ ∈ problem10Feasible p r y α, quasiIntegral (fun z : X × X => f z.1) γ) ≠ ⊤ ∧
      (⨆ γ ∈ problem10Feasible p r y α, quasiIntegral (fun z : X × X => f z.1) γ) ≠ ⊥) :
    ∃ γ ∈ problem10Feasible p r y α, quasiIntegral (fun z : X × X => f z.1) γ =
      ⨆ γ' ∈ problem10Feasible p r y α, quasiIntegral (fun z : X × X => f z.1) γ' := by sorry

end WassersteinLinOpt.Ball
