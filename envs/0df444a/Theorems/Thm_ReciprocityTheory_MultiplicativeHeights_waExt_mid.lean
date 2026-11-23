-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_waExt_mid
-- name    : ReciprocityTheory.MultiplicativeHeights.waExt_mid
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:56:11.480363+00:00
-- url     : https://prove2.me/theorems/38bd7a67-6406-41e1-b6b5-b4ffc5687ca2
-- title:
--   Multiplicative Heights: wa Ext mid
-- statement:
--   The Multiplicative Heights construction uses the wa Ext mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegAB.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegAB.lean#L29-L31

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Module

theorem ReciprocityTheory.MultiplicativeHeights.waExt_mid {α : Type} {n : ℕ} (x y : α) (f : Fin n → α) (j : Fin n) :
    waExt x y f (Fin.castSucc j).succ = f j := by sorry
