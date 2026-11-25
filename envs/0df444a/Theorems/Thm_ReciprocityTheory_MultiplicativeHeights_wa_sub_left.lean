-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_sub_left
-- name    : ReciprocityTheory.MultiplicativeHeights.wa_sub_left
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:05:51.272174+00:00
-- url     : https://prove2.me/theorems/076844c7-c8b8-441f-bb9d-47432f517519
-- title:
--   Multiplicative Heights: wa sub left
-- statement:
--   The Multiplicative Heights construction uses the wa sub left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegAA.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegAA.lean#L41-L43

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

theorem ReciprocityTheory.MultiplicativeHeights.wa_sub_left {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y z : Fin r → K) : S.h (x - y) z = S.h x z - S.h y z := by sorry
