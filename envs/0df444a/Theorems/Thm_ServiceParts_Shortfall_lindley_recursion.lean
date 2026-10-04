-- Prove2me | Theorems.Thm_ServiceParts_Shortfall_lindley_recursion
-- name    : ServiceParts.Shortfall.lindley_recursion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T23:24:20.277588+00:00
-- url     : https://prove2.me/theorems/ce0fcb8a-6d98-4df3-b45e-8579b396eea5
-- title:
--   Eq. (8.1) — under the modified (s–1, s) policy the shortfall s − Iₙ follows Vₙ = [Vₙ₋₁ + Dₙ − c]⁺
-- statement:
--   Consider the capacity-limited system of Section 8.1 under the modified $(s-1, s)$ policy with target level $s$: starting from net inventory $I_0 = s$, in period $n$ the facility produces $\min\{c, s - I_{n-1} + D_n\}$ units after observing the demand $D_n$, so that
--   $$I_n = I_{n-1} - D_n + \min\{c,\ s - I_{n-1} + D_n\}.$$
--   Then for every period $n \ge 0$ and every outcome, the shortfall $s - I_n$ equals $V_n$, where $V_0 = 0$ and
--   $$V_n = \left[V_{n-1} + D_n - c\right]^+ .$$
--   In particular the shortfall does not depend on the target level $s$.
--
--   This identity is Equation (8.1): it reduces the inventory dynamics under the modified base-stock policy to a single recursion, the Lindley recursion, on which every later result of the chapter rests.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 184-185, Section 8.1.1, Eq. (8.1)

import Mathlib
import Definitions.Def_ServiceParts_Shortfall_ShortfallModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace ServiceParts.Shortfall

/-- Eq. (8.1), Muckstadt (2005), p. 185. Under the modified `(s–1, s)` policy with target level
`s`, started with no shortfall, the shortfall `s − I_n` at the end of every period `n` equals
`V_n`, the solution of `V_0 = 0`, `V_n = [V_{n−1} + D_n − c]^+`; in particular it does not depend
on `s`. -/
theorem lindley_recursion {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : ShortfallModel Ω P) (s : ℝ) (n : ℕ) (ω : Ω) :
    s - M.netInventory s n ω = M.shortfall n ω := by sorry

end ServiceParts.Shortfall
