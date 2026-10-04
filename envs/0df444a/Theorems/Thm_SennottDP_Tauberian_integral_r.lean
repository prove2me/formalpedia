-- Prove2me | Theorems.Thm_SennottDP_Tauberian_integral_r
-- name    : SennottDP.Tauberian.integral_r
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T13:11:27.104974+00:00
-- url     : https://prove2.me/theorems/d6f037b7-e63b-433d-9f02-83914f080fed
-- title:
--   Eq. (A.26) — ∫_0^1 r(x) dx = ∫_{1/e}^1 dx/x = 1
-- statement:
--   For the function $r$ of Fig. A.1 ($r(x) = 1/x$ for $x \ge e^{-1}$ and $0$ below),
--   $$\int_0^1 r(x)\,dx = \int_{e^{-1}}^{1} \frac{dx}{x} = 1.$$
--
--   This normalisation is why Karamata's argument with $f = r$ returns exactly the limit $L$ of the Abel means.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 280, Eq. (A.26)

import Mathlib
import Definitions.Def_SennottDP_Tauberian_PowerSeries
import Definitions.Def_SennottDP_Tauberian_KaramataR

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.Tauberian

/-- Sennott (1999), p. 280, Eq. (A.26): `∫_0^1 r(x) dx = ∫_{e^{-1}}^1 dx/x = 1`. -/
theorem integral_r :
    ∫ x in (0 : ℝ)..1, r x = ∫ x in Real.exp (-1)..1, x⁻¹ ∧
      ∫ x in Real.exp (-1)..1, x⁻¹ = 1 := by sorry

end SennottDP.Tauberian
