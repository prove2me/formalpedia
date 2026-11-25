-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_valDiv2
-- name    : ReciprocityTheory.ChartRestriction.L1.valDiv2
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:02:15.177833+00:00
-- url     : https://prove2.me/theorems/69bfc2dc-4530-5058-8a4a-773abe52f3d0
-- title:
--   L1: val Div2
-- statement:
--   The L1 construction uses the val Div2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/Norm1728EqOneOfFiveLe.lean#L45-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/Norm1728EqOneOfFiveLe.lean#L45-L148

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedValA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedValB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKerProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKurOmega
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_Norm1728EqOneOfFiveLe
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

theorem ReciprocityTheory.ChartRestriction.L1.valDiv2 (d : ℕ) (L : PeriodPair) (hsq : Squarefree d) (hd4 : d % 4 = 3) (hCM : HasCMBy d L) (l : ℕ)
    [Fact l.Prime] (h5 : 5 ≤ l) (hld : ¬ l ∣ d) (ι : ℂ ≃+* ℂ_[l]) (hJ : ι (jInv L) ∈ MaximalUnramifiedExtension l)
    (hJ1 : ‖ι (jInv L)‖ ≤ 1) (h0 : ι (jInv L) ≠ 1728) :
    ∃ m : ℤ, ‖ι (jInv L) - 1728‖ = (l : ℝ) ^ (2 * m) := by sorry
