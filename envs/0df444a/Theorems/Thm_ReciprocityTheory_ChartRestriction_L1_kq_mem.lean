-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kq_mem
-- name    : ReciprocityTheory.ChartRestriction.L1.kq_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:46:19.756411+00:00
-- url     : https://prove2.me/theorems/8e7002bc-f039-5fe6-b790-3f30a343fe29
-- title:
--   L1: kq mem
-- statement:
--   The L1 construction uses the kq mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormSqrtNegPowPrimeSqSub.lean#L116-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormSqrtNegPowPrimeSqSub.lean#L116-L173

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurNewton
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormSqrtNegPowPrimeSqSub
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
variable (l : ℕ) [Fact l.Prime]
variable {l}

theorem ReciprocityTheory.ChartRestriction.L1.kq_mem (d : ℕ) (hl : l ≠ 2) (hld : ¬ l ∣ d)
    (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(d : ZMod l)) (δ : ℂ_[l]) (hδ : δ ^ 2 = -(d : ℂ_[l]))
    (hn : ‖δ‖ = 1) : δ ∈ MaximalUnramifiedExtension l := by sorry
