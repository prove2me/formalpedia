-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kerProdAt_of_norm
-- name    : ReciprocityTheory.ChartRestriction.L1.kerProdAt_of_norm
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:47:15.853966+00:00
-- url     : https://prove2.me/theorems/e92619d5-4d27-45fa-97ec-7af9e1682faa
-- title:
--   L1: ker Prod At of norm
-- statement:
--   The L1 construction uses the ker Prod At of norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedKerPrin.lean#L30-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedKerPrin.lean#L30-L57

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKerPoly
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HasCMByStable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKerPrin
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

theorem ReciprocityTheory.ChartRestriction.L1.kerProdAt_of_norm (d : ℕ) (L : PeriodPair) (hCM : HasCMBy d L) (l e r : ℕ) (hodd : Odd (r ^ 2 + d))
    (hl : ¬ l ∣ r ^ 2 + d) (he : ¬ e ∣ r ^ 2 + d) (he' : ¬ e ∣ (r ^ 2 + d - 1) / 2) :
    KerProdAt d L l e := by sorry
