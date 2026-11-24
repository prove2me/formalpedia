-- Prove2me | Theorems.Thm_SensitivityGraphPopulation_minimumEdges_copy_cost
-- name    : SensitivityGraphPopulation.minimumEdges_copy_cost
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T20:19:20.462804+00:00
-- url     : https://prove2.me/theorems/f5d03e5c-f4a4-4d32-9c94-4f6b3b41976a
-- title:
--   Optimal outgoing-incidence allowance in the copy bound
-- statement:
--   Let $n,m,d$ be nonnegative integers and let $\alpha>0$. Write $E(t,\alpha)$ for the integral minimum-edge function, and let
--
--   $$b=\max\{0,n-(m+1)\alpha\}.$$
--
--   Then, with subtraction in the arguments truncated at zero,
--
--   $$mb+E(n-b,\alpha)\le md+E(\max\{0,n-d\},\alpha).$$
--
--   Thus $b$ minimizes this expression over all nonnegative outgoing allowances $d$.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/MinimumEdgesConvexity.lean lines 70–111; SHA256 eaf246265953537261f4ef8b4a21268f2c95a2fcafe3dd1f4483385adc4f11ee; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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

theorem SensitivityGraphPopulation.minimumEdges_copy_cost (size outgoing alpha marks : ℕ) (hpos : 0 < alpha) :
    let best := size - (marks + 1) * alpha
    marks * best + minimumEdges (size - best) alpha ≤
      marks * outgoing + minimumEdges (size - outgoing) alpha := by sorry
