-- Prove2me | Theorems.Thm_ServiceParts_Shortfall_stationary_shortfall_exists
-- name    : ServiceParts.Shortfall.stationary_shortfall_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T23:26:24.356423+00:00
-- url     : https://prove2.me/theorems/e89ab7c2-4aa0-446d-a973-3b4c08b24dae
-- title:
--   Section 8.1.1 — for E[D] < c the shortfall process has a stationary law, that of V = supₙ Σ(Dₖ − c)
-- statement:
--   In the capacity-limited system of Section 8.1, with i.i.d. nonnegative demands $D_1, D_2, \dots$ and $E[D] < c$, let $V_n$ be the shortfall process started from $V_0 = 0$ and let
--   $$V = \sup_{n \ge 0} \sum_{k=1}^{n} (D_k - c).$$
--   Then:
--
--   1. $V$ is finite with probability one;
--   2. for every real $v$,
--   $$\lim_{n \to \infty} P\{V_n > v\} = P\{V > v\};$$
--   3. the law of $V$ is stationary for the recursion (8.1): if $D$ is a demand independent of $V$, then $[V + D - c]^+$ has the same law as $V$, that is, for every real $v$,
--   $$P\{V > v\} = \int P\{[x + D - c]^+ > v\}\, P_V(dx).$$
--
--   This is the book's statement "a stationary distribution exists for the shortfall process. Let $V$ represent this random variable": it identifies the stationary shortfall with the maximum of the random walk with increments $D_k - c$, which is the object Theorem 11 describes.
--
--   **Formalization Note** The stationary law is pinned to the limit law of $V_n$ started from $V_0 = 0$ (the initial condition of p. 185), and item 3 states its stationarity through the law $\mu_D$ of $D_1$: $P\{V > v\} = \int \mu_D\{d : [V(\omega) + d - c]^+ > v\}\, P(d\omega)$.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 184, Section 8.1.1 (existence of the stationary shortfall); p. 185 (V_0 = 0)

import Mathlib
import Definitions.Def_ServiceParts_Shortfall_ShortfallModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace ServiceParts.Shortfall

/-- Section 8.1.1, p. 184 (and Section 8.1.2, p. 185, `V_0 = 0`). Since `E[D] < c` and the demands
are i.i.d., the shortfall process has a stationary distribution, the law of
`V = sup_{n ≥ 0} ∑_{k=1}^{n} (D_k − c)`:
1. `V` is finite almost surely;
2. for every `v`, `P{V_n > v} → P{V > v}` as `n → ∞`, where `V_n` is the shortfall process
   started from `V_0 = 0`;
3. the law of `V` is stationary for (8.1): if `D` is a demand independent of `V`, then
   `[V + D − c]^+` has the law of `V`. -/
theorem stationary_shortfall_exists {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : ShortfallModel Ω P) :
    P {ω | M.walkMax ω = ⊤} = 0 ∧
    (∀ v : ℝ, Tendsto (fun n : ℕ => P {ω | v < M.shortfall n ω}) atTop
        (𝓝 (P {ω | v < M.stationaryShortfall ω}))) ∧
    (∀ v : ℝ, P {ω | v < M.stationaryShortfall ω} =
        ∫⁻ ω, (P.map (M.demand 1))
          {d : ℝ | v < max (M.stationaryShortfall ω + d - M.capacity) 0} ∂P) := by sorry

end ServiceParts.Shortfall
