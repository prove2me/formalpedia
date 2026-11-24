-- Prove2me | Theorems.Thm_SensitivityGraphPopulation_minimumEdges_succ
-- name    : SensitivityGraphPopulation.minimumEdges_succ
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T20:19:19.551433+00:00
-- url     : https://prove2.me/theorems/801afbae-344c-489c-934f-d9219a796e4f
-- title:
--   Successive differences of the integral minimum-edge function
-- statement:
--   For integers $n\ge0$ and $\alpha>0$, define
--
--   $$E(n,\alpha)=\alpha\binom{\lfloor n/\alpha\rfloor}{2}
--    +(n\bmod\alpha)\lfloor n/\alpha\rfloor.$$
--
--   Then
--
--   $$E(n+1,\alpha)=E(n,\alpha)+\lfloor n/\alpha\rfloor.$$
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/MinimumEdgesConvexity.lean lines 10–29; SHA256 eaf246265953537261f4ef8b4a21268f2c95a2fcafe3dd1f4483385adc4f11ee; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_IntegralGraphPopulation
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SensitivityGraphPopulation
end SensitivityGraphPopulation


/-! Discrete convexity of the exact minimum-edge function. -/
open SensitivityGraphPopulation
open scoped Classical
set_option autoImplicit false

theorem SensitivityGraphPopulation.minimumEdges_succ (n alpha : ℕ) (hpos : 0 < alpha) :
    minimumEdges (n + 1) alpha = minimumEdges n alpha + n / alpha := by sorry
