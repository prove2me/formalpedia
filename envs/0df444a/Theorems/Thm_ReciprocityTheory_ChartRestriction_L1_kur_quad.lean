-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kur_quad
-- name    : ReciprocityTheory.ChartRestriction.L1.kur_quad
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:27:27.292173+00:00
-- url     : https://prove2.me/theorems/51c18810-35ce-41a8-a002-07bdb6fffad2
-- title:
--   L1: kur quad
-- statement:
--   The L1 construction uses the kur quad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormSqrtNegPowPrimeSqSub.lean#L177-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormSqrtNegPowPrimeSqSub.lean#L177-L258

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
variable (l)

theorem ReciprocityTheory.ChartRestriction.L1.kur_quad (d : ℕ) (hd : d % 4 = 3) (hl : l ≠ 2) (hld : ¬ l ∣ d)
    (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(d : ZMod l)) (a : ℂ_[l])
    (ha : a ^ 2 - a + (((d + 1) / 4 : ℕ) : ℂ_[l]) = 0) :
    ‖a‖ ≤ 1 ∧ ‖1 - 2 * a‖ = 1 ∧ ∃ ha' : a ∈ MaximalUnramifiedExtension l, ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, FrobField (MaximalUnramifiedExtension l) l σ →
      σ ⟨a, ha'⟩ = 1 - ⟨a, ha'⟩ := by sorry
