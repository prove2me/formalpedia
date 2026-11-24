-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_newton_exists_poly
-- name    : ReciprocityTheory.ChartRestriction.L1.newton_exists_poly
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:35:31.909039+00:00
-- url     : https://prove2.me/theorems/e7511454-e640-415c-91ea-a01d3ccb99d8
-- title:
--   L1: newton exists poly
-- statement:
--   The L1 construction uses the newton exists poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/KurNewton.lean#L32-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/KurNewton.lean#L32-L38

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

theorem ReciprocityTheory.ChartRestriction.L1.newton_exists_poly (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) :
    ∃ Q : Polynomial (newtonBall K), Q.map (newtonBall K).subtype = P := by sorry
