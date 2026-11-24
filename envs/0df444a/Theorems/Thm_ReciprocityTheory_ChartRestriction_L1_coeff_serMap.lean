-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_coeff_serMap
-- name    : ReciprocityTheory.ChartRestriction.L1.coeff_serMap
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:06:35.234002+00:00
-- url     : https://prove2.me/theorems/737e29fa-9441-4654-a08c-ada0023477d7
-- title:
--   L1: coeff ser Map
-- statement:
--   The L1 construction uses the coeff ser Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedProj.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedProj.lean#L20-L22

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedProjA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedProj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
variable {E : Type} [Field E]

theorem ReciprocityTheory.ChartRestriction.L1.coeff_serMap (ψ : E →+ E) (S : PowerSeries E) (n : ℕ) :
    PowerSeries.coeff n (serMap ψ S) = ψ (PowerSeries.coeff n S) := by sorry
