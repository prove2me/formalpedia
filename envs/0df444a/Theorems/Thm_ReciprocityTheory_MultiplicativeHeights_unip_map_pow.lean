-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_unip_map_pow
-- name    : ReciprocityTheory.MultiplicativeHeights.unip_map_pow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:05:21.847107+00:00
-- url     : https://prove2.me/theorems/1456dacb-b364-4152-8a71-8eb3281bacf3
-- title:
--   Multiplicative Heights: unip map pow
-- statement:
--   The Multiplicative Heights construction uses the unip map pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/Unipotent.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/Unipotent.lean#L29-L34

import Definitions.Def_ReciprocityTheory_SemistableReduction_UnipotentA
import Definitions.Def_ReciprocityTheory_SemistableReduction_UnipotentB
import Definitions.Def_ReciprocityTheory_SemistableReduction_Unipotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField Polynomial

theorem ReciprocityTheory.MultiplicativeHeights.unip_map_pow {K : Type*} [Field K] {r : ℕ} (σ : K →+* ℂ) (M : Matrix (Fin r) (Fin r) K)
    (n : ℕ) : (M.map σ) ^ n = (M ^ n).map σ := by sorry
