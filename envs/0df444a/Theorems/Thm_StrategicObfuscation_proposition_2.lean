-- Prove2me | Theorems.Thm_StrategicObfuscation_proposition_2
-- name    : StrategicObfuscation.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:52:56.501615+00:00
-- url     : https://prove2.me/theorems/4454e7a2-a695-43bf-9a61-92e4ec0a13dc
-- title:
--   Proposition 2 — more resources for reviewers may backfire (corrected: $0<p<1$)
-- statement:
--   Let $0<c<V$, $g>0$, $0<p<1$, let $\pi$ be a detection probability, $e(\alpha,\sigma)$ an effort selection and $(\alpha^*,Q^*)$ any equilibrium family, with equilibrium effort $e^*$ and sponsor's payoff $u_S$ as functions of $\sigma$.
--
--   1. If $pV\le c$, $u_S$ is strictly increasing on $[0,1]$. If $pV>c$, $u_S$ is strictly increasing on $[0,\bar\sigma_1)$ and on $(\bar\sigma_2,1]$.
--   2. At every $\sigma\in(0,1)$ at which $e^*$ is differentiable and $\pi$ is differentiable within $[0,1]\times[0,\infty)$ at $(\sigma,e^*(\sigma))$,
--
--   $$u_S'(\sigma)<0\iff pV>c,\ \ \sigma\in(\bar\sigma_1,\bar\sigma_2)\ \text{ and }\ \frac{\partial\pi(\sigma,e^*)}{\partial\sigma}+\frac{\partial\pi(\sigma,e^*)}{\partial e}\frac{\partial e^*}{\partial\sigma}<0.\tag{5}$$
--
--   Moreover, more resources can backfire: for some such instance and equilibrium family there are $\bar\sigma_1<\sigma<\sigma'<\bar\sigma_2$ with $u_S(\sigma')<u_S(\sigma)$.
--
--   The sponsor gains from more examination resources when the reviewer has few or many of them. At moderate resources, the applicant's induced obfuscation can outweigh the reviewer's better detection.
--
--   **Formalization Note** The differentiability at $\sigma$ is what (5) needs to mean anything. `deriv` is $0$ where $u_S$ is not differentiable, so the left side is then false.
--
--   Differences from the source:
--   - correction: p unrestricted → 0 < p < 1; reason: at p = 1, u_S is constant while every condition of the iff can hold (π(σ,e) = σ exp(1 − (1+e)²), g = 1, V = 2, c = 1); at p = 0, u_S = 0, so more resources never make the sponsor better off
--   - generalization: Assumption 1 with ∂²π/∂σ∂e < 0 for a twice differentiable π → IsDetection: monotonicity plus decreasing differences in σ, strict whenever π(σ,·) separates the two efforts; reason: the C² class satisfies it by integrating the mixed partial, and the paper's own example on p.14, which the strict form excludes, also satisfies it
--   - encoding: e(α, σ) written as a function → a fixed selection E with IsEffort π g E; reason: the argmax in (1) may not be a singleton; every selection is covered and existence of a maximizer stays part of the hypothesis, as in (1)
--   - encoding: Bayes' rule (2) as a quotient → (2) cross-multiplied in IsEquilibrium; reason: the same equation whenever the denominator is nonzero; at σ = 1, e = 0 the report is off path and a PBE leaves Q free, where Lean's 0/0 = 0 would pin it
--   - reading: "very small or a very large amount of resources" → u_S strictly increasing on all of [0,1] if pV ≤ c, and on [0,σ̄1) and (σ̄2,1] if pV > c; reason: this is the complement of the region in the iff and what the proof shows; with σ̄1 = 0 the first interval is empty
--   - reading: "decreasing in σ" at a point, with partials of π and e* → deriv u_S σ < 0 at σ ∈ (0,1) where e* and π are differentiable; reason: the proof reads the sign of a derivative, and (5) can change sign inside (σ̄1, σ̄2) as in the example at σ = 1/2; the derivative needs an open interval, and part 1 covers the endpoints; at e* = 0 the partial in e is one-sided
--   - reading: "can backfire" → an instance, an equilibrium family and σ < σ' in (σ̄1, σ̄2) with u_S(σ') < u_S(σ); reason: an existence claim; the paper's example on p.14 is the witness
--   - reading: σ̄2 is the root of f → σ̄2 is sup{σ ∈ [0,1] : f(σ) > 0}; reason: the two agree when f is continuous, and the supremum keeps the goal free of a continuity hypothesis
-- source:
--   Figueroa & Lemus, The Benefit of the Doubt: Decision Making under Strategic Obfuscation, SSRN 3840423 (version of April 4, 2022), Proposition 2, p.13

import Mathlib
import Definitions.Def_StrategicObfuscation_IsDetection
import Definitions.Def_StrategicObfuscation_IsEffort
import Definitions.Def_StrategicObfuscation_IsEquilibriumFamily
import Definitions.Def_StrategicObfuscation_equilibriumPayoff
import Definitions.Def_StrategicObfuscation_sigmaBarOne
import Definitions.Def_StrategicObfuscation_sigmaBarTwo
import Definitions.Def_StrategicObfuscation_conditionFiveLHS

open Set

namespace StrategicObfuscation

/-- **Proposition 2: more resources for reviewers may backfire (corrected: `0 < p < 1`).**
Figueroa & Lemus, *The Benefit of the Doubt: Decision Making under Strategic Obfuscation*,
SSRN 3840423 (version of April 4, 2022), Proposition 2, p.13 (PDF p.13).

For all parameters with `0 < c < V`, `0 < g`, `0 < p < 1`, every detection probability `π`, every
effort selection `E` and every equilibrium family `(αS, QS)`, writing `e*` and `u_S` for the
equilibrium effort and payoff:
1. if `pV ≤ c`, `u_S` is strictly increasing on `[0, 1]`; if `pV > c`, it is strictly increasing on
   `[0, σ̄1)` and on `(σ̄2, 1]`;
2. at every `σ ∈ (0, 1)` where `e*` is differentiable and `π` is differentiable within
   `[0, 1] × [0, ∞)` at `(σ, e*(σ))`, `u_S' (σ) < 0` iff `pV > c`, `σ ∈ (σ̄1, σ̄2)` and (5) holds.

Moreover, more resources can backfire: there are an instance, an equilibrium family and
`σ < σ'` in `(σ̄1, σ̄2)` with `u_S(σ') < u_S(σ)`.

**Formalization Note** `0 < p < 1` corrects the printed statement, which leaves `p` free: at `p = 1`
the iff fails, since `u_S` is constant while (5) can hold, and at `p = 0` one has `u_S = 0`. Assumption 1
is in the difference form of `IsDetection`, which covers the paper's `C²` class and its example. The
differentiability at `σ` is what (5) needs in order to mean anything, and `deriv` returns `0` where
`u_S` is not differentiable. The iff is on the open interval because "decreasing" is read through a
two-sided derivative; the endpoints are covered by part 1. Every equilibrium family is covered, as
equilibrium is not unique at `pV = c`. -/
theorem proposition_2 :
    (∀ (V c g p : ℝ) (π : ℝ → ℝ → ℝ) (E : ℝ → ℝ → ℝ) (αS QS : ℝ → ℝ),
      0 < c → c < V → 0 < g → 0 < p → p < 1 → IsDetection π → IsEffort π g E →
      IsEquilibriumFamily π V c p E αS QS →
      (p * V ≤ c → StrictMonoOn (equilibriumPayoff π V c p E αS) (Icc 0 1)) ∧
      (c < p * V →
        StrictMonoOn (equilibriumPayoff π V c p E αS) (Ico 0 (sigmaBarOne E)) ∧
        StrictMonoOn (equilibriumPayoff π V c p E αS) (Ioc (sigmaBarTwo π V c p E) 1)) ∧
      (∀ σ ∈ Ioo (0 : ℝ) 1,
        DifferentiableAt ℝ (equilibriumEffort E αS) σ →
        DifferentiableWithinAt ℝ (Function.uncurry π) (Icc 0 1 ×ˢ Ici 0)
          (σ, equilibriumEffort E αS σ) →
        (deriv (equilibriumPayoff π V c p E αS) σ < 0 ↔
          c < p * V ∧ sigmaBarOne E < σ ∧ σ < sigmaBarTwo π V c p E ∧
            conditionFiveLHS π (equilibriumEffort E αS) σ < 0))) ∧
    (∃ (V c g p : ℝ) (π : ℝ → ℝ → ℝ) (E : ℝ → ℝ → ℝ) (αS QS : ℝ → ℝ),
      0 < c ∧ c < V ∧ 0 < g ∧ 0 < p ∧ p < 1 ∧ IsDetection π ∧ IsEffort π g E ∧
      IsEquilibriumFamily π V c p E αS QS ∧
      ∃ σ σ' : ℝ, sigmaBarOne E < σ ∧ σ < σ' ∧ σ' < sigmaBarTwo π V c p E ∧
        equilibriumPayoff π V c p E αS σ' < equilibriumPayoff π V c p E αS σ) := by sorry

end StrategicObfuscation
