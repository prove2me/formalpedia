-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_velu_pair
-- name    : ReciprocityTheory.ChartRestriction.L1.velu_pair
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:48:39.561846+00:00
-- url     : https://prove2.me/theorems/f2926d32-a41a-4019-b5dd-8ecc0f7d5d5a
-- title:
--   L1: velu pair
-- statement:
--   The L1 construction uses the velu pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedVeluFun.lean#L11-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedVeluFun.lean#L11-L31

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

theorem ReciprocityTheory.ChartRestriction.L1.velu_pair (L : PeriodPair) (z P : ℂ) (hz : z ∉ L.lattice) (hP : P ∉ L.lattice)
    (hp : z + P ∉ L.lattice) (hm : z - P ∉ L.lattice) :
    (L.weierstrassP (z + P) - L.weierstrassP P) + (L.weierstrassP (z + -P) - L.weierstrassP (-P))
      = fW L.g₂ L.g₃ (L.weierstrassP P) / (L.weierstrassP z - L.weierstrassP P) ^ 2
        + fW' L.g₂ (L.weierstrassP P) / (2 * (L.weierstrassP z - L.weierstrassP P)) := by sorry
