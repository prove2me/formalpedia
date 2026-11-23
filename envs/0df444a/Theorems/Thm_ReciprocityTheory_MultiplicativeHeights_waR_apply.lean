-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_waR_apply
-- name    : ReciprocityTheory.MultiplicativeHeights.waR_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:50:55.796483+00:00
-- url     : https://prove2.me/theorems/6d64383f-2ab6-43cb-a074-b16b5224cb17
-- title:
--   Multiplicative Heights: wa R apply
-- statement:
--   The Multiplicative Heights construction uses the wa R apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegAA.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegAA.lean#L18-L19

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAA
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

theorem ReciprocityTheory.MultiplicativeHeights.waR_apply {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y : Fin r → K) : waR S x y = S.h x y := by sorry
