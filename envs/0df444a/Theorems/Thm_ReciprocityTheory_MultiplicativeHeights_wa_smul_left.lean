-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_smul_left
-- name    : ReciprocityTheory.MultiplicativeHeights.wa_smul_left
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:05:23.556978+00:00
-- url     : https://prove2.me/theorems/f3b974f2-1990-4612-b16a-da5fa0287118
-- title:
--   Multiplicative Heights: wa smul left
-- statement:
--   The Multiplicative Heights construction uses the wa smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegAA.lean#L45-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegAA.lean#L45-L48

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

theorem ReciprocityTheory.MultiplicativeHeights.wa_smul_left {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (a : K) (x y : Fin r → K) : S.h (a • x) y = S.c a * S.h x y := by sorry
