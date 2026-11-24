-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ker_norm
-- name    : ReciprocityTheory.ChartRestriction.L1.ker_norm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:55:12.56183+00:00
-- url     : https://prove2.me/theorems/14f3a1d4-d172-4c17-877c-6edb8b9448d7
-- title:
--   L1: ker norm
-- statement:
--   The L1 construction uses the ker norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedHalf.lean#L97-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedHalf.lean#L97-L105

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedHalf
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
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
variable {L : PeriodPair} {α : ℂ} {T : Finset ℂ}

theorem ReciprocityTheory.ChartRestriction.L1.ker_norm (hs : MulStable L α) {N : ℕ} (hN : Complex.normSq α = N) {z : ℂ}
    (hz : α * z ∈ L.lattice) : (N : ℂ) * z ∈ L.lattice := by sorry
