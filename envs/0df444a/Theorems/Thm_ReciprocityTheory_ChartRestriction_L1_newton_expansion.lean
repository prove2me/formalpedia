-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_newton_expansion
-- name    : ReciprocityTheory.ChartRestriction.L1.newton_expansion
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:35:59.412771+00:00
-- url     : https://prove2.me/theorems/4a63be6d-b864-481f-b5cb-c74a8258f11a
-- title:
--   L1: newton expansion
-- statement:
--   The L1 construction uses the newton expansion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/KurNewton.lean#L45-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/KurNewton.lean#L45-L57

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurNewton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem ReciprocityTheory.ChartRestriction.L1.newton_expansion (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) (x y : K)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ∃ k : K, ‖k‖ ≤ 1 ∧ P.eval (x + y) = P.eval x + P.derivative.eval x * y + k * y ^ 2 := by sorry
