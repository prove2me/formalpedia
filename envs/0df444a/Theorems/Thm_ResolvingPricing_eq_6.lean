-- Prove2me | Theorems.Thm_ResolvingPricing_eq_6
-- name    : ResolvingPricing.eq_6
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:26:50.308173+00:00
-- url     : https://prove2.me/theorems/ab48e585-e487-492c-9392-f660708d7781
-- title:
--   Eq. (6): the inventory path through harmonic series
-- statement:
--   Consider any admissible run from the normalized initial inventory $x_T$, with normalized inventories $x_\tau=y_\tau/\tau$, demand rates $\lambda_\tau$, $\Delta_\tau=\lambda_\tau-x_\tau$, noises $\xi_\tau$ and lost sales $\ell_\tau$. Then, at every sample point,
--   $$x_\tau=x_T-\bar\Delta_{\to\tau}-\bar\xi_{\to\tau}+\bar\ell_{\to\tau}\qquad\text{for all }1\le\tau\le T.$$
--
--   The identity writes the inventory path through the harmonic series of the decisions, the noises and the lost sales; it is the starting point of the comparison between the optimal policy and the resolving heuristic.
--
--   **Formalization Note** The identity is pathwise and uses no assumption on the model.
--
--   Differences from the source:
--   - generalization: stated for the optimal policy π* → every admissible run, every initial x and every sample point, with no assumption on the model; reason: the identity is a pathwise consequence of the inventory dynamics x_{τ−1} = x_τ − (Δ_τ + ξ_τ − ℓ_τ)/(τ − 1); π* is one such run
--   - reading: A4: the conditional distribution of ξ_t given p_t is Q(p_t) → the conditional law of ξ_t given the past ℱ_{t+1} is Q(p_t) (condExp of indicators of Borel sets); reason: the Bellman equation (5) and the recursion (7), p.3543, take the expectation over ξ ~ Q(price) given the current state, and the network analogue B4 (p.3549) states independence from past noise; under the weaker reading Q does not determine R^π(T, x_T)
--   - encoding: prices p ∈ [p̲, p̄] with demand f(p) and noise law Q(p) → demand rates λ ∈ [d̲, d̄] with price g(λ) = f⁻¹(λ) and noise law Q(λ) := Q(f⁻¹(λ)); |f(p) − f(p′)| = |λ − λ′| in A5; reason: the paper's own parametrization in (5); f is a bijection [p̲, p̄] → [d̲, d̄], so the instances are the same
-- source:
--   Y. Wang, H. Wang, Constant Regret Resolving Heuristics for Price-Based Revenue Management, Oper. Res. 70(6):3538–3557 (2022), doi:10.1287/opre.2021.2219, §4.1, Eq. (6), p.3543 (PDF p.7)

import Mathlib
import Definitions.Def_ResolvingPricing_Run

open MeasureTheory

namespace ResolvingPricing

/-- **Eq. (6)**, Y. Wang, H. Wang, *Constant Regret Resolving Heuristics for Price-Based Revenue Management*,
Oper. Res. 70(6) (2022), p.3543: along the path of a policy,
`x_τ = x_T − Δ̄→τ − ξ̄→τ + ℓ̄→τ` for all `1 ≤ τ ≤ T`, where `Δ_τ = λ_τ − x_τ`, `ℓ_τ` are the lost
sales and `Δ̄→τ`, `ξ̄→τ`, `ℓ̄→τ` the harmonic series of p.3543.

**Formalization Note.** The paper states (6) for the optimal policy `π*`; it is a pathwise identity of
the inventory dynamics and is stated here for every run, every `x`, and every sample point, with no
assumption on the model. The paper's `x_T` is `x` (the run starts from `y_T = x T`). -/
theorem eq_6 (P : Model) (T : ℕ) (x : ℝ) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (π : Run P T x μ ℱ) (ω : Ω) (τ : ℕ) (hτ1 : 1 ≤ τ)
    (hτT : τ ≤ T) :
    π.xB τ ω = x - harm T (fun t => π.DeltaB t ω) τ - harm T (fun t => π.xiB t ω) τ
      + harm T (fun t => π.lostB t ω) τ := by sorry

end ResolvingPricing
