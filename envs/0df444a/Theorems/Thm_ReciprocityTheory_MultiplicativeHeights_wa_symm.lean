-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_symm
-- name    : ReciprocityTheory.MultiplicativeHeights.wa_symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:27.163213+00:00
-- url     : https://prove2.me/theorems/1892b18a-d21a-4883-8ab0-9aa5318237ac
-- title:
--   Multiplicative Heights: wa symm
-- statement:
--   The Multiplicative Heights construction uses the wa symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegAA.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegAA.lean#L21-L26

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

theorem ReciprocityTheory.MultiplicativeHeights.wa_symm {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y : Fin r → K) : S.h y x = S.c (S.h x y) := by sorry
