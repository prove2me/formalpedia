-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_phiM_mem
-- name    : ReciprocityTheory.ChartRestriction.L1.phiM_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:46:02.571797+00:00
-- url     : https://prove2.me/theorems/3ad261a3-dd69-4b68-8817-2732ab80bc2e
-- title:
--   L1: phi M mem
-- statement:
--   The L1 construction uses the phi M mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/MuMEvalPowEqZero.lean#L94-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/MuMEvalPowEqZero.lean#L94-L96

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_MuMEvalPowEqZero
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
open Formalism.L2.Th1.CM Polynomial
variable (l : ℕ) [Fact l.Prime]

theorem ReciprocityTheory.ChartRestriction.L1.phiM_mem (f : MonoidAlgebra ℤ (muM l)) : phiM l f ∈ Rmu l := by sorry
