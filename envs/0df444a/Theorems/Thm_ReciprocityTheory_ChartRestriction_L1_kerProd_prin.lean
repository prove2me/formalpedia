-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kerProd_prin
-- name    : ReciprocityTheory.ChartRestriction.L1.kerProd_prin
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:47:01.224074+00:00
-- url     : https://prove2.me/theorems/3e2240a5-c4fd-5916-a5b8-45c6e4a2b218
-- title:
--   L1: ker Prod prin
-- statement:
--   The L1 construction uses the ker Prod prin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedKerPrin.lean#L59-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedKerPrin.lean#L59-L90

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

theorem ReciprocityTheory.ChartRestriction.L1.kerProd_prin (d : ℕ) (L : PeriodPair) (hd4 : d % 4 = 3) (hCM : HasCMBy d L) (l : ℕ) (hl : l.Prime)
    (h5 : 5 ≤ l) (hld : ¬ l ∣ d) (e : ℕ) (he : e = 2 ∨ e = 3 ∧ ¬ 3 ∣ d) : KerProdAt d L l e := by sorry
