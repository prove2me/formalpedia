-- Prove2me | Theorems.Thm_ServiceParts_Shortfall_shortfall_tail_recursion
-- name    : ServiceParts.Shortfall.shortfall_tail_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T23:28:28.841854+00:00
-- url     : https://prove2.me/theorems/74997d72-dd1a-41b9-a07e-5f8ced0a2ff2
-- title:
--   Eq. (8.2) — P{Vₙ > v} = P{Dₙ > v + c} + E_D[1(d ≤ v + c)·P{Vₙ₋₁ > v + c − d}] for v > 0
-- statement:
--   In the capacity-limited system of Section 8.1, let $V_n$ be the shortfall process ($V_0 = 0$, $V_n = [V_{n-1} + D_n - c]^+$). For every period $n \ge 1$ and every $v > 0$,
--   $$P\{V_n > v\} = P\{V_{n-1} + D_n - c > v\} = P\{D_n > v + c\} + E_D\!\left[1(d \le v + c)\cdot P\{V_{n-1} > v + c - d\}\right],$$
--   where $E_D$ integrates $d$ against the law of $D_n$ and $1(A)$ is the indicator of $A$.
--
--   Equation (8.2) is the integral equation from which the tail of the shortfall distribution is computed; in the stationary regime it is the equation behind Theorem 11 and the mass-exponential approximations of Section 8.1.3.
--
--   **Formalization Note** The book writes the inner probability as the conditional probability given $D_n = d$; since $V_{n-1}$ depends only on $D_1, \dots, D_{n-1}$, which are independent of $D_n$, it equals the unconditional $P\{V_{n-1} > v + c - d\}$, and that is what is stated. Periods are indexed $n + 1$ in Lean.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 189-190, Section 8.1.3, Eq. (8.2)

import Mathlib
import Definitions.Def_ServiceParts_Shortfall_ShortfallModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace ServiceParts.Shortfall

/-- Eq. (8.2), Muckstadt (2005), p. 190. For `v > 0` and every period `n + 1 ≥ 1`,
`P{V_{n+1} > v} = P{V_n + D_{n+1} − c > v}
  = P{D_{n+1} > v + c} + E_D[1(d ≤ v + c) · P{V_n > v + c − d}]`,
the expectation being over the law of `D_{n+1}` (by independence of `V_n` and `D_{n+1}` the
conditional probability given `D_{n+1} = d` is the unconditional one). -/
theorem shortfall_tail_recursion {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : ShortfallModel Ω P) (n : ℕ) (v : ℝ) (hv : 0 < v) :
    P {ω | v < M.shortfall (n + 1) ω} =
        P {ω | v < M.shortfall n ω + M.demand (n + 1) ω - M.capacity} ∧
    P {ω | v < M.shortfall n ω + M.demand (n + 1) ω - M.capacity} =
        P {ω | v + M.capacity < M.demand (n + 1) ω} +
          ∫⁻ d, (Set.Iic (v + M.capacity)).indicator
              (fun x => P {ω | v + M.capacity - x < M.shortfall n ω}) d
            ∂(P.map (M.demand (n + 1))) := by sorry

end ServiceParts.Shortfall
