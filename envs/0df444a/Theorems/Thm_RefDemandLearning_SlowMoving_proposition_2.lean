-- Prove2me | Theorems.Thm_RefDemandLearning_SlowMoving_proposition_2
-- name    : RefDemandLearning.SlowMoving.proposition_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T05:25:16.569191+00:00
-- url     : https://prove2.me/theorems/69a9629d-ad91-465f-98dd-cf98d2f51a63
-- title:
--   Proposition 2 — generalized conditions for asymptotic optimality
-- statement:
--   Fix a price interval $[\ell,u]$ with $0\le\ell<u$ and the known parameter rectangle of Section 2. Its loss-averse subset $\Theta$ has $\alpha\ge0$, $\beta>0$, $0\le\eta^+\le\eta^-$, nonnegative expected demand throughout the box, and $\ell<\alpha/(2\beta)<u$ for every parameter vector in $\Theta$. Demand is $d(p,r,\theta)=\alpha-\beta p+\eta^+(r-p)^+-\eta^-(p-r)^+$ and revenue is $R=p d$.
--
--   Use the actual policy $S$ with $n_i=2^i$, $\delta_i=c_0 2^{-i/4}$, $0<c_0<2^{-3/4}(u-\ell)$, and initial estimates in the known intercept and slope intervals. Its clipped two-price experiments and projected least-squares updates use only the latest complete episode's observations. On any probability space, the shocks are measurable iid real variables of mean zero, finite variance, and a finite MGF in some neighborhood of zero. The law is unknown to the policy. Regret is the full dynamic clairvoyant supremum minus expected cumulative revenue of this causal run.
--
--   Let $\rho$ be a continuous interval-valued reference mechanism. Suppose there are finite $c_4,c_5>0$ such that, uniformly in $T\ge1$ and $\vartheta\in\Theta$,
--   $$\Delta_{\mathrm{fixed}}\!\left(\frac{\vartheta_\alpha}{2\vartheta_\beta};T,\rho,\vartheta\right)\le c_4\sqrt T,$$
--   and for all positive integers $s<t$, every feasible history $h$ of length $s$, and every held price $p\in[\ell,u]$,
--   $$\sum_{k=s+1}^{t}|\rho_k(h,p,\ldots,p)-p|\le c_5\sqrt{t-s}.$$
--   For each fixed $\theta\in\Theta$, there exists a finite $c_6>0$, independent of the horizon, such that
--   $$\Delta_S(T,\rho,\theta)\le c_6\sqrt T\qquad\text{for every integer }T\ge1.$$
--   These are sufficient mechanism conditions for the learning policy's regret guarantee. They are hypotheses of this proposition only.
--
--   **Formalization Note.** The existential constants $c_4,c_5$ precede all of their uniform quantifiers. The conclusion's constant may depend on the fixed model, mechanism, noise law and tuning, but not on $T$.
--
--   Differences from the source:
--   - encoding: periods start at 1 and positive integer horizons → period n represents source period n+1; horizons and interval endpoints retain explicit positive-natural guards; reason: finite histories use Fin n and finite sums are reindexed without changing any term
--   - encoding: episodewise unconstrained least-squares argmin and subsequent componentwise projection → the unique two-block least-squares formula with the same coordinate projections and interval-valued prices in a causal prefix recursion; reason: both blocks have equal positive length and distinct prices; only the most recent complete episode is used; the center is interior under the standing assumptions, so full interval clipping equals the printed one-sided clipping
--   - generalization: policy histories in (2.5) have nonnegative demand coordinates → the same policy rule is defined for all real observations; reason: the additive-noise model permits negative realizations; the extension agrees on every nonnegative history and does not truncate demand
--   - encoding: dynamic finite-horizon supremum and expected cumulative revenue → a real supremum over the whole compact price box and a Bochner integral on a probability space; reason: the concrete Borel causal recursion has bounded finite-horizon revenues, so the integral and supremum are the ordinary finite values
--   - reading: the display writes continuous real-valued functions without repeating their codomain → reference maps take values in the price interval; reason: Section 2 and the immediately preceding definition of reference mechanisms supply this codomain
-- source:
--   den Boer and Keskin, Dynamic Pricing with Demand Learning and Reference Effects, DOI https://doi.org/10.1287/mnsc.2021.4234, supplied April 19, 2021 artifact, Proposition 2, printed p. 17, PDF p. 17

import Definitions.Def_RefDemandLearning_SlowMoving_Mechanism
import Definitions.Def_RefDemandLearning_SlowMoving_Model
import Definitions.Def_RefDemandLearning_SlowMoving_Noise
import Definitions.Def_RefDemandLearning_SlowMoving_Policy
import Definitions.Def_RefDemandLearning_SlowMoving_Regret

set_option autoImplicit false
open MeasureTheory

namespace RefDemandLearning.SlowMoving

theorem proposition_2 (B : Bounds) (hB : Standing B) (ρ : Mechanism B.prices)
    (hconditions : ∃ c₄ c₅ : ℝ, 0 < c₄ ∧ 0 < c₅ ∧
      (∀ T : ℕ, 1 ≤ T → ∀ θ : Parameters, InTheta B θ →
        fixedRegret B ρ θ (optimalBasePrice θ) T ≤ c₄ * Real.sqrt T) ∧
      (∀ s t : ℕ, 1 ≤ s → s < t → ∀ (h : Fin s → Price B.prices) (p : Price B.prices),
        trackingError ρ s t h p ≤ c₅ * Real.sqrt (t - s : ℕ)))
    (θ : Parameters) (hθ : InTheta B θ) (c₀ a₀ b₀ : ℝ)
    (hpolicyTuning : TuningOK B c₀ a₀ b₀)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → Ω → ℝ) (hnoise : AdmissibleNoise P ε) :
    ∃ c₆ : ℝ, 0 < c₆ ∧ ∀ T : ℕ, 1 ≤ T →
      regret B ρ θ c₀ a₀ b₀ P ε T ≤ c₆ * Real.sqrt T := by sorry

end RefDemandLearning.SlowMoving
