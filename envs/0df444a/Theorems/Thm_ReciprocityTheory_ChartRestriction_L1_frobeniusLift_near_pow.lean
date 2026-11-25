-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_frobeniusLift_near_pow
-- name    : ReciprocityTheory.ChartRestriction.L1.frobeniusLift_near_pow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:49:22.093943+00:00
-- url     : https://prove2.me/theorems/af3889cc-eeea-4483-9883-cd7762fae464
-- title:
--   L1: frobenius Lift near pow
-- statement:
--   The L1 construction uses the frobenius Lift near pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ExistsExtendEndomorphismFractions.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ExistsExtendEndomorphismFractions.lean#L21-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_MuMEvalPowEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsExtendEndomorphismFractions
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

theorem ReciprocityTheory.ChartRestriction.L1.frobeniusLift_near_pow (s : Rmu l →+* Rmu l)
    (hs : ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l),
      ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) (x : Rmu l) :
    ‖((s x : Rmu l) : ℂ_[l]) - (x : ℂ_[l]) ^ l‖ ≤ ‖(l : ℂ_[l])‖ := by sorry
