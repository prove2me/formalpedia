-- Prove2me | Theorems.Thm_PolySampIso_lemma_24
-- name    : PolySampIso.lemma_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:28:20.386611+00:00
-- url     : https://prove2.me/theorems/53b1513d-6fff-43ba-944d-4edc4e353429
-- title:
--   Lemma 24, p.37 — Phase 1 of Algorithm 5 is δ/2-close in TV to a 3-warm start for π_{t₁}
-- statement:
--   Let $X$ be a nonempty bounded polytope in $\mathbb R^n$, $\delta\in(0,\tfrac12)$, $D=n+\log(8/\delta)$ and $t_1=10^6D^3$. Let $\hat x\in X$ satisfy $\|\nabla\psi(\hat x)\|_{\hat x,*}\le1/(100\sqrt{t_1D})$ (the guarantee of AnalyticCenter), and let $x$ be the output of Phase 1 of Algorithm 5: $x\sim\mathcal N(\hat x,t_1^{-1}H(\hat x)^{-1})$, replaced by $\hat x$ if $\|x-\hat x\|_{\hat x}>4\sqrt{D/t_1}$. Then there is a probability measure $\mu$ on $X$ with
--
--   $$\mathrm{TV}(\mathrm{Law}(x),\mu)\le\frac\delta2,\qquad\chi^2(\mu\|\pi_{t_1})\le3.$$
--
--   So a single Gaussian draw at an approximate analytic center starts the cooling schedule warm, with no warmness assumption on the input.
--
--   Differences from the source:
--   - generalization: x̂ ← AnalyticCenter(X, 1/(100√(tD))) (Algorithm 5, line 3) → any x̂ ∈ X with ‖∇ψ(x̂)‖_{x̂,∗} ≤ 1/(100√(t₁D)); reason: the proof uses only this guarantee (Proposition 5); AnalyticCenter's output is such a point
--   - encoding: µ ∈ P(X); Law(x) → a probability measure µ on ℝⁿ with µ(Xᶜ) = 0; Law(x) = phase1Law (Mathlib's multivariateGaussian pushed forward by the rejection of lines 5–6); reason: the same objects
--   - encoding: δ (Algorithm 5's input) → δ ∈ (0, ½); reason: Algorithm 5's input line
--   - encoding: the standing assumption of §2.3 (a nonempty, full-dimensional, bounded polytope; A full-rank) → X = {Ax < b} nonempty and bounded, n ≥ 1; reason: X is open, so nonempty means full-dimensional; nonempty and bounded imply full column rank
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), Lemma 24, p.37 (PDF p.39); Algorithm 5, Phase 1, p.33

import Mathlib
import Definitions.Def_PolySampIso_Divergences
import Definitions.Def_PolySampIso_LogBarrier
import Definitions.Def_PolySampIso_FunctionalCooling

open MeasureTheory ProbabilityTheory

namespace PolySampIso

/-- **Lemma 24** (Phase 1 of Algorithm 5 is close to a warm start for `π_{t₁}`).

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), Lemma 24, p.37 (PDF p.39):

"Lemma 24. Let x be the output of Phase 1 of Algorithm 5. There exists µ ∈ P(X) such that
TV (Law(x), µ) ≤ δ/2, χ2 (µ∥πt1) ≤ 3."

**Formalization Note.** Phase 1 (lines 2–7 of Algorithm 5): `D = n + log(8/δ)`, `t₁ = 10⁶D³`,
`x̂ = AnalyticCenter(X, 1/(100√(t₁D)))`, `x ∼ N(x̂, t₁⁻¹H(x̂)⁻¹)`, and `x ← x̂` if
`‖x − x̂‖_x̂ > 4√(D/t₁)`. `x̂` is any point of `X` with the guarantee of Proposition 5,
`‖∇ψ(x̂)‖_{x̂,∗} ≤ 1/(100√(t₁D))`, the only property of AnalyticCenter the proof uses.
`Law(x) = phase1Law A b δ x̂`. `µ ∈ P(X)` is a probability measure with `µ(Xᶜ) = 0`; `χ²` is in
`ℝ≥0∞`. `δ ∈ (0, ½)` is Algorithm 5's input; the standing assumption of §2.3 is kept. -/
theorem lemma_24 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hX : StandingAssumption A b) (hn : 0 < n) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2)
    (xhat : EuclideanSpace ℝ (Fin n)) (hxhat : xhat ∈ polytope A b)
    (hcenter : dualLocalNorm A b xhat (gradLogBarrier A b xhat) ≤
      1 / (100 * Real.sqrt (coolT1 n δ * coolD n δ))) :
    ∃ μ : Measure (EuclideanSpace ℝ (Fin n)), IsProbabilityMeasure μ ∧ μ (polytope A b)ᶜ = 0 ∧
      tvDist (phase1Law A b δ xhat) μ ≤ δ / 2 ∧ chiSq μ (cooled A b (coolT1 n δ)) ≤ 3 := by sorry

end PolySampIso
