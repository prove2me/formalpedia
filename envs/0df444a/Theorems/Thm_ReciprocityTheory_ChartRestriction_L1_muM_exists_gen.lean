-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_muM_exists_gen
-- name    : ReciprocityTheory.ChartRestriction.L1.muM_exists_gen
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:45:01.366479+00:00
-- url     : https://prove2.me/theorems/4d7addc2-d94a-4051-b60e-e4f717ffd676
-- title:
--   L1: mu M exists gen
-- statement:
--   The L1 construction uses the mu M exists gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/MuMEvalPowEqZero.lean#L40-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/MuMEvalPowEqZero.lean#L40-L51

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

theorem ReciprocityTheory.ChartRestriction.L1.muM_exists_gen (n : ℕ) (hn : 0 < n) :
    ∃ g : ℂ_[l], g ^ n = 1 ∧ ∀ a : ℂ_[l], a ^ n = 1 → ∃ k : ℕ, g ^ k = a := by sorry
