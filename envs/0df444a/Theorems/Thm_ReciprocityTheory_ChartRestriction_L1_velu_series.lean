-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_velu_series
-- name    : ReciprocityTheory.ChartRestriction.L1.velu_series
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:59:38.674006+00:00
-- url     : https://prove2.me/theorems/7005f19d-89ec-4c87-bcae-5b58a11b855f
-- title:
--   L1: velu series
-- statement:
--   The L1 construction uses the velu series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedSeries.lean#L109-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedSeries.lean#L109-L128

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedVeluFun
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedVeluAlg
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinRecursion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedSeries
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
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.velu_series (L : PeriodPair) (α : ℂ) (T : Finset ℂ) (hα : α ≠ 0) (hs : MulStable L α)
    (hT : IsHalfReps L α T) :
    PowerSeries.rescale α (wpNum L.g₂ L.g₃)
        * homS (wpNum L.g₂ L.g₃) (2 * (xsOf L T).card) (rootPoly (xsOf L T) ^ 2)
      = homS (wpNum L.g₂ L.g₃) (2 * (xsOf L T).card + 1) (veluNum L.g₂ L.g₃ (xsOf L T)) := by sorry
