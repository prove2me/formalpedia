-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_le_one_of_root
-- name    : ReciprocityTheory.ChartRestriction.L1.norm_le_one_of_root
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:48:07.054992+00:00
-- url     : https://prove2.me/theorems/0db6ec8f-3ed7-5e71-bba7-60bc5d3b378e
-- title:
--   L1: norm le one of root
-- statement:
--   The L1 construction uses the norm le one of root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModJInt.lean#L11-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModJInt.lean#L11-L41

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_Interface
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_IsIntegralOfRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormLeOneOfIntegralInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.norm_le_one_of_root {l : ℕ} [Fact l.Prime] {x : ℂ_[l]} (P : Polynomial ℤ) (hm : P.Monic)
    (h : P.eval₂ (Int.castRingHom ℂ_[l]) x = 0) : ‖x‖ ≤ 1 := by sorry
