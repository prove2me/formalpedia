-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_coeff_mem_X
-- name    : ReciprocityTheory.ChartRestriction.L1.coeff_mem_X
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:45:08.267142+00:00
-- url     : https://prove2.me/theorems/ab468c9d-cb9e-531f-912b-2f253fc8aa25
-- title:
--   L1: coeff mem X
-- statement:
--   The L1 construction uses the coeff mem X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedProj.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedProj.lean#L61-L66

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

theorem ReciprocityTheory.ChartRestriction.L1.coeff_mem_X : ∀ n, PowerSeries.coeff n (PowerSeries.X : PowerSeries E) ∈ k := by sorry
