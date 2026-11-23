-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_unip_normSq_col
-- name    : ReciprocityTheory.MultiplicativeHeights.unip_normSq_col
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:54.689622+00:00
-- url     : https://prove2.me/theorems/1f7ba19e-39ae-4184-af64-6f964f02f579
-- title:
--   Multiplicative Heights: unip norm Sq col
-- statement:
--   The Multiplicative Heights construction uses the unip norm Sq col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/UnipotentB.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/UnipotentB.lean#L18-L23

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_UnipotentB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix

theorem ReciprocityTheory.MultiplicativeHeights.unip_normSq_col {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (j : Fin r) :
    normSq (M *ᵥ Pi.single j 1) = ∑ i, ‖M i j‖ ^ 2 := by sorry
