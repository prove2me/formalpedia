-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CardG_card_line
-- name    : ReciprocityTheory.ChartRestriction.L1.CardG.card_line
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:44:31.316303+00:00
-- url     : https://prove2.me/theorems/f8af3d24-3ca5-5c80-8d08-eb90d83b66ee
-- title:
--   Card G: card line
-- statement:
--   The Card G construction uses the card line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedCardG.lean#L13-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedCardG.lean#L13-L39

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedHalf
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MulStableIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedCardG
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
open ReciprocityTheory.ChartRestriction.L1.CardG

theorem ReciprocityTheory.ChartRestriction.L1.CardG.card_line {F : Type} [Field F] [Fintype F] (u v : F) (h : u ≠ 0 ∨ v ≠ 0) :
    (Finset.univ.filter (fun w : F × F => u * w.1 + v * w.2 = 0)).card = Fintype.card F := by sorry
