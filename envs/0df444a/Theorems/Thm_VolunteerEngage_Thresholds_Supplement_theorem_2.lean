-- Prove2me | Theorems.Thm_VolunteerEngage_Thresholds_Supplement_theorem_2
-- name    : VolunteerEngage.Thresholds.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:17:06.080799+00:00
-- url     : https://prove2.me/theorems/a9067f99-5c83-460f-b842-36f4617889ae
-- title:
--   Theorem 2 (corrected at τ₁), p. 23 — admissibility, optimality and average cost β
-- statement:
--   Let $M$ satisfy the standing assumptions, let $(\beta,v)$ be any solution of (68)–(69), and let $\tau_l\ge0$ satisfy $v(\tau_l)=p-\hat c_l$ for $1\le l\le L$, with $\tau_{L+1}=0$. Let $\theta^*_{\tau}$ be the nested policy (72), defined from those thresholds. Then it is admissible and equals $\psi(p-v(z))$ for every $z\ge0$. For every filtered probability space and every workload process under that policy,
--
--   $$\lim_{t\to\infty}\frac1t\mathbb E\!\left[\int_0^t c(\theta^*_{\tau}(W(s)))\,ds+pU(t)\right]=\beta.$$
--
--   For every admissible stationary Markov policy $\theta$, on its own arbitrary filtered probability space, every workload process under $\theta$ satisfies
--
--   $$\beta\le\liminf_{t\to\infty}\frac1t\mathbb E\!\left[\int_0^t c(\theta(W(s)))\,ds+pU(t)\right].$$
--
--   Thus no admissible policy has a smaller limit-superior objective (53). This connects the analytic Bellman solution to an optimal engagement policy.
--
--   **Formalization Note** The two cost clauses quantify independently over the probability space, filtration, Brownian motion and workload process. Neither existence nor uniqueness is asserted. Expected costs take values in $[0,\infty]$; no integrability or asymptotic moment hypotheses are assumed.
--
--   Differences from the source:
--   - encoding: the queueing primitives and standing assumptions of §§2–3 → M.Standing at every theorem; reason: it expands to L≥1, θ0<0, η_l>0, 0<c_1<⋯<c_L<p and p,κ,σ>0; these are the inherited model assumptions, with no θ_L≥0 restriction
--   - generalization: the solution (β*,v) obtained in Theorem 1 → every solution of the published IsBellmanSol; reason: the conclusions use only (68)–(69), and specialize to the solution furnished by Theorem 1
--   - correction: the final branch of (72) uses τ_1<z, leaving z=τ_1 undefined → θ0 on z≥τ_1; reason: (70) and (E8) give ψ(c_1)=θ0; the sentence after (75) says do nothing for W≥w*_1; no input is excluded
--   - generalization: long-run average cost and optimality for the limsup objective (53) → a true limit for the candidate and a liminf lower bound for competitors; reason: these stronger assertions are proved explicitly on Online Supplement pp. 8–9, including (C6)
--   - encoding: the inverse thresholds (71) → nonnegative τ_l with v(τ_l)=p−chat_l, and τ_{L+1}=0; reason: strict monotonicity uniquely determines these thresholds, exactly as in the published Proposition 3
--   - encoding: reflected workload problem with expected nonnegative cost → every weak solution of (54)–(57), with cost in [0,∞]; reason: no solution map or moment premise is postulated; independent probability spaces retain the full stationary Markov comparison class
--   - encoding: (54)–(57) under a stationary Markov policy θ(W(s)) → IsWorkload: X a (0,σ²) Brownian motion for 𝔽 with X(0)=0, W and U adapted, almost surely W continuous on [0,∞), U(0)=0, the extension of U by 0 to negative times a Stieltjes function (nondecreasing, right-continuous) whose measure charges no time in [0,t] with W>0, and (54)–(55) for every t≥0; policies are Borel on [0,∞) with values in A; reason: the time integral of θ(W(s)) needs a measurable integrand; under (54)–(57) U cannot jump (a jump would make W>0 at a charged time), so U and W are continuous and no solution is excluded; X(0)=0 is the empty initial sign-up list of p. 12
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, p. 23, Theorem 2; pp. 22–23, (70)–(72), (75)–(76); Online Supplement pp. 8–9, liminf bound and (C6)

import Mathlib
import Definitions.Def_VolunteerEngage_Thresholds_Supplement_Policy
import Definitions.Def_VolunteerEngage_Thresholds_Supplement_RelativeValue
import Definitions.Def_VolunteerEngage_Thresholds_Supplement_Workload

namespace VolunteerEngage.Thresholds.Supplement

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Theorem 2, p. 23, and the stronger liminf bound and true limit proved in
§C, Online Supplement pp. 8–9. Each cost clause quantifies independently over
all spaces and all weak solutions of (54)–(57). No existence is asserted. -/
theorem theorem_2 (M : Model) (hM : M.Standing) (β : ℝ) (v v' : ℝ → ℝ)
    (hv : IsBellmanSol M β v v') (τ : ℕ → ℝ) (hτL : τ (M.L + 1) = 0)
    (hτ : ∀ l ∈ Finset.Icc 1 M.L, 0 ≤ τ l ∧ v (τ l) = M.p - chat M l) :
    IsAdmissible M (candidate M τ) ∧
    (∀ z : ℝ, 0 ≤ z → candidate M τ z = feedback M v z) ∧
    (∀ {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (𝔽 : Filtration ℝ mΩ) (X W U : ℝ → Ω → ℝ),
      IsWorkload M P 𝔽 (candidate M τ) X W U →
      Tendsto (avgCost M P (candidate M τ) W U) atTop (𝓝 (ENNReal.ofReal β))) ∧
    (∀ {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (𝔽 : Filtration ℝ mΩ) (θ : ℝ → ℝ), IsAdmissible M θ →
      ∀ X W U : ℝ → Ω → ℝ, IsWorkload M P 𝔽 θ X W U →
      ENNReal.ofReal β ≤ liminf (avgCost M P θ W U) atTop) := by sorry

end VolunteerEngage.Thresholds.Supplement
