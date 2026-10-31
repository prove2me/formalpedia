-- Prove2me | Theorems.Thm_SuperPareto_eq_10
-- name    : SuperPareto.eq_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:16:17.426338+00:00
-- url     : https://prove2.me/theorems/622b42db-de38-4b63-bc2f-baa7e5618982
-- title:
--   Display (10), p.9 — $f(Y)\le_{\mathrm{st}}\sum\theta_if(Y_i)$, strictly with two positive weights
-- statement:
--   Let $Y_1,\dots,Y_n$ be weakly negatively associated random variables with the Pareto(1) law, $Y\sim\mathrm{Pareto}(1)$ on the same space, $(\theta_1,\dots,\theta_n)\in\Delta_n$, and $f$ increasing, convex and non-constant. Then
--
--   $$
--   f(Y)\le_{\mathrm{st}}\sum_{i=1}^n\theta_if(Y_i), \tag{10}
--   $$
--
--   and if $\theta_i>0$ for at least two indices $i$, then $f(Y)<_{\mathrm{st}}\sum_{i=1}^n\theta_if(Y_i)$, i.e. $P(f(Y)>t)<P(\sum_i\theta_if(Y_i)>t)$ for every $t$ with $P(f(Y)>t)\in(0,1)$.
--
--   This is step (c) of the proof of Theorem 1: by Lemma 1, part (i) of the theorem for WNAID super-Pareto losses reduces to (10), including its strict version.
--
--   **Formalization Note** $\le_{\mathrm{st}}$ is the platform definition `StarShapedRisk.LawInvariant.FSD`, $<_{\mathrm{st}}$ is `StrictStochLE` (§2.2). The strict clause covers $t=f(1)$ when $f$ is constant on an interval to the right of $1$, where $f(Y)$ has an atom at its essential infimum. $Y$ need not be independent of the $Y_i$.
--
--   Differences from the source:
--   - reading: the strictness sentence writes P(∑θᵢf(Xᵢ) > t) > P(f(X) > t) → f(Yᵢ) and f(Y); reason: the sentence is about the Pareto variables Y, Yᵢ of (10); the Xᵢ are only equal in law to f(Yᵢ), and f(Xᵢ) is a slip
--   - reading: the strictness argument covers t > f(1) and concludes "the strictness statement after (4) also holds" → f(Y) <st ∑θᵢf(Yᵢ) at every t with P(f(Y) > t) ∈ (0, 1); reason: <st is defined on p.5 over all such t; the two differ only at t = f(1) when f is flat to the right of 1, where the claim is still true
--   - generalization: n ≥ 2 random variables on an atomless probability space (standing assumptions, p.4) → a finite index type ι of any size (n = 1 allowed) on any probability space; reason: the paper's case n ≥ 2 on an atomless space is a special case; for n = 1 the statement holds trivially
--   - reading: decreasing sets S ⊆ ℝ^{n−1} in Definition 2 (weak negative association) → measurable (Borel) decreasing sets in `IsWNA`; reason: P(X₋ᵢ ∈ S) is defined only for measurable S; as a hypothesis this quantifies over fewer sets, so the theorem is at least as strong
--   - encoding: P(X₋ᵢ ∈ S | Xᵢ ≤ x) ≤ P(X₋ᵢ ∈ S) for x with P(Xᵢ ≤ x) > 0 (display (2)) → P(X₋ᵢ ∈ S, Xᵢ ≤ x) ≤ P(X₋ᵢ ∈ S) · P(Xᵢ ≤ x) for every x; reason: equivalent when P(Xᵢ ≤ x) > 0; when P(Xᵢ ≤ x) = 0 the product form reads 0 ≤ 0
--   - encoding: an increasing convex function f with unstated domain (Definition 1, Lemmas 1–2) → f : ℝ → ℝ, Monotone and ConvexOn ℝ univ; reason: an increasing convex function on [1, ∞) (or [0, ∞)) extends to ℝ keeping both properties and non-constancy, and only its values on the support matter
--   - encoding: random variables and events → measurable functions Ω → ℝ and measurable sets; reason: a random variable is a measurable function; Lean states measurability explicitly
-- source:
--   Chen, Embrechts, Wang, An unexpected stochastic dominance: Pareto distributions, dependence, and diversification, arXiv:2208.08471v4, §2.3, step (c), display (10) and the strictness sentence after it, p.9

import Mathlib
import Definitions.Def_StarShapedRisk_LawInvariant_VaR
import Definitions.Def_SuperPareto_IsWNA
import Definitions.Def_SuperPareto_StrictStochLE

open MeasureTheory ProbabilityTheory

namespace SuperPareto

/-- **Display (10), with the strictness statement.** Chen, Embrechts, Wang, *An unexpected
stochastic dominance*, arXiv:2208.08471v4, §2.3, step (c), display (10), p.9: for weakly
negatively associated `Y₁, …, Yₙ ∼ Pareto(1)`, `Y ∼ Pareto(1)`, `(θ₁, …, θₙ) ∈ Δₙ` and an
increasing, convex, non-constant `f`,
`f(Y) ≤st ∑ θᵢ f(Yᵢ)`  (10),
and `f(Y) <st ∑ θᵢ f(Yᵢ)` when `θᵢ > 0` for at least two `i` ("Hence, the strictness statement
after (4) also holds").

**Formalization Note.** `FSD P X Z` (platform definition `StarShapedRisk.LawInvariant.FSD`) means
`X ≤st Z`; `StrictStochLE P X Z` is `X <st Z` (§2.2, p.5), which quantifies over every `t` with
`P(f(Y) > t) ∈ (0, 1)`, including `t = f(1)` when `f` is flat at `1`. The page writes `f(Xᵢ)`, `f(X)`
in the strictness sentence; `f(Yᵢ)`, `f(Y)` are meant. Pareto(1) is `paretoMeasure 1 1`; `Δₙ` is
`stdSimplex ℝ ι`. `Y` lives on the same probability space, with no independence assumption. -/
theorem eq_10 {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    [Fintype ι] (Y : Ω → ℝ) (Ys : ι → Ω → ℝ) (hY : Measurable Y) (hYs : ∀ i, Measurable (Ys i))
    (hWNA : IsWNA P Ys) (hlawY : P.map Y = paretoMeasure 1 1)
    (hlaw : ∀ i, P.map (Ys i) = paretoMeasure 1 1)
    (θ : ι → ℝ) (hθ : θ ∈ stdSimplex ℝ ι)
    (f : ℝ → ℝ) (hfmono : Monotone f) (hfconv : ConvexOn ℝ Set.univ f) (hfnc : ∃ a b, f a ≠ f b) :
    StarShapedRisk.LawInvariant.FSD P (fun ω => f (Y ω)) (fun ω => ∑ i, θ i * f (Ys i ω)) ∧
      ((∃ i j, i ≠ j ∧ 0 < θ i ∧ 0 < θ j) →
        StrictStochLE P (fun ω => f (Y ω)) (fun ω => ∑ i, θ i * f (Ys i ω))) := by sorry

end SuperPareto
