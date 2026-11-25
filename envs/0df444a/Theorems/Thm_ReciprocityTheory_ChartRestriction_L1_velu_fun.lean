-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_velu_fun
-- name    : ReciprocityTheory.ChartRestriction.L1.velu_fun
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:48:57.345478+00:00
-- url     : https://prove2.me/theorems/5e9d5736-307b-5483-9ef9-b930a80384f6
-- title:
--   L1: velu fun
-- statement:
--   The L1 construction uses the velu fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedVeluFun.lean#L33-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedVeluFun.lean#L33-L55

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedHalf
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ExistsFinitePartOneIdeleSplitCongruenceQuotient
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedVeluFun
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

theorem ReciprocityTheory.ChartRestriction.L1.velu_fun (L : PeriodPair) (α : ℂ) (T : Finset ℂ) (hα : α ≠ 0) (hs : MulStable L α)
    (hT : IsHalfReps L α T) (z : ℂ) (hz : α * z ∉ L.lattice) :
    α ^ 2 * L.weierstrassP (α * z) = veluFun L.g₂ L.g₃ (xsOf L T) (L.weierstrassP z) := by sorry
