-- Prove2me | Theorems.Thm_VolunteerEngage_Thresholds_Supplement_lemma_1
-- name    : VolunteerEngage.Thresholds.Supplement.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:14:49.96589+00:00
-- url     : https://prove2.me/theorems/83b08fa2-dc10-4942-b249-63f23d516eca
-- title:
--   Lemma 1, Online Supplement p. 7 — mean-zero stochastic integral and sublinear terminal expectation
-- statement:
--   Let $M$ satisfy the standing assumptions, let $(\beta,v)$ solve (68)–(69), and set $f(z)=\int_0^zv(s)\,ds-pz$. Under any admissible stationary Markov policy $\theta$ and any workload process $(X,W,U)$ satisfying (54)–(57) on any filtered probability space, put $B=X/\sigma$. Then both parts hold:
--
--   1. For every version $J$ of the Itô integral $J(t)=\int_0^t(v(W(s))-p)\,dB(s)$ and every $t\ge0$, $J(t)$ is integrable and
--      $$\mathbb E[J(t)]=0.$$
--   2. For every $t\ge0$, $f(W(t))$ is integrable, and
--      $$\lim_{t\to\infty}\frac{\mathbb E[f(W(t))]}{t}=0.$$
--
--   This removes the martingale and terminal terms in the average-cost verification argument. No moment bound, finiteness of expected idleness or terminal expectation limit is a premise.
--
--   **Formalization Note** The published `EthierKurtz.HasBrownianItoIntegral` supplies the stochastic integral relation on nonnegative real time. The filtration and $X/\sigma$ are restricted to those times; all versions satisfying that relation are covered. The $Z$ of §C is $W$.
--
--   Differences from the source:
--   - encoding: the queueing primitives and standing assumptions of §§2–3 → M.Standing at every theorem; reason: it expands to L≥1, θ0<0, η_l>0, 0<c_1<⋯<c_L<p and p,κ,σ>0; these are the inherited model assumptions, with no θ_L≥0 restriction
--   - generalization: the solution (β*,v) obtained in Theorem 1 → every solution of the published IsBellmanSol; reason: the conclusions use only (68)–(69), and specialize to the solution furnished by Theorem 1
--   - reading: Z and B in §C → the workload W and the standard Brownian motion X/σ; reason: (54) and (C4) identify the process and its noise
--   - encoding: expectations of a stochastic integral and f(W(t)) → integrability in the conclusions before the Bochner expectations; reason: excludes default-zero integrals; integrability follows from bounded v−p, mean reversion and bounded control, and is not an additional premise
--   - encoding: Itô integral at t≥0 → every J satisfying the published step-approximation relation, with time ℝ≥0; reason: this is the same integral up to almost-sure equality; the underlying filtration is not restricted to a natural filtration
--   - encoding: (54)–(57) under a stationary Markov policy θ(W(s)) → IsWorkload: X a (0,σ²) Brownian motion for 𝔽 with X(0)=0, W and U adapted, almost surely W continuous on [0,∞), U(0)=0, the extension of U by 0 to negative times a Stieltjes function (nondecreasing, right-continuous) whose measure charges no time in [0,t] with W>0, and (54)–(55) for every t≥0; policies are Borel on [0,∞) with values in A; reason: the time integral of θ(W(s)) needs a measurable integrand; under (54)–(57) U cannot jump (a jump would make W>0 at a charged time), so U and W are continuous and no solution is excluded; X(0)=0 is the empty initial sign-up list of p. 12
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, Online Supplement pp. 7–8, Lemma 1, (C1), (C4)

import Mathlib
import Definitions.Def_VolunteerEngage_Thresholds_Supplement_RelativeValue
import Definitions.Def_VolunteerEngage_Thresholds_Supplement_Workload
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral

namespace VolunteerEngage.Thresholds.Supplement

open MeasureTheory Filter Topology
open scoped NNReal

/-- Lemma 1, Online Supplement p. 7. Z in §C is W. B = X/σ is standard.
Integrability is asserted, never assumed, for both expectations. -/
theorem lemma_1 (M : Model) (hM : M.Standing) (β : ℝ) (v v' : ℝ → ℝ)
    (hv : IsBellmanSol M β v v') {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (𝔽 : Filtration ℝ mΩ)
    (θ : ℝ → ℝ) (hθ : IsAdmissible M θ) (X W U : ℝ → Ω → ℝ)
    (hW : IsWorkload M P 𝔽 θ X W U) :
    (∀ J : ℝ≥0 → Ω → ℝ,
      EthierKurtz.HasBrownianItoIntegral P (fun t => 𝔽 (t : ℝ))
        (fun t ω => X t ω / M.σ) (fun t ω => v (W t ω) - M.p) J →
      ∀ t : ℝ≥0, Integrable (J t) P ∧ (∫ ω, J t ω ∂P) = 0) ∧
    (∀ t : ℝ, 0 ≤ t → Integrable (fun ω => relativeValue M v (W t ω)) P) ∧
    Tendsto (fun t : ℝ => (∫ ω, relativeValue M v (W t ω) ∂P) / t) atTop (𝓝 0) := by sorry

end VolunteerEngage.Thresholds.Supplement
