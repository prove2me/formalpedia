-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_serMap_C
-- name    : ReciprocityTheory.ChartRestriction.L1.serMap_C
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:48:36.901306+00:00
-- url     : https://prove2.me/theorems/29681c5e-f746-48bc-a3d7-2091aae65988
-- title:
--   L1: ser Map C
-- statement:
--   The L1 construction uses the ser Map C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedProj.lean#L78-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedProj.lean#L78-L83

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
variable (k : Subfield E)
variable {k}

theorem ReciprocityTheory.ChartRestriction.L1.serMap_C (ψ : E →+ E) (q : E) : serMap ψ (PowerSeries.C q) = PowerSeries.C (ψ q) := by sorry
