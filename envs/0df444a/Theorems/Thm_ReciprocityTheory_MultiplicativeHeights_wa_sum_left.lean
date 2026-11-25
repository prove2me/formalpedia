-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_sum_left
-- name    : ReciprocityTheory.MultiplicativeHeights.wa_sum_left
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:05:13.668738+00:00
-- url     : https://prove2.me/theorems/28cdc2ff-9d3e-4d6f-a6f9-34b730d472c5
-- title:
--   Multiplicative Heights: wa sum left
-- statement:
--   The Multiplicative Heights construction uses the wa sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegAA.lean#L56-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegAA.lean#L56-L61

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

theorem ReciprocityTheory.MultiplicativeHeights.wa_sum_left {K : Type} [Field K] [NumberField K] {r n : ℕ} (S : HermForm K r)
    (y : Fin r → K) (t : Fin n → K) (b : Fin n → Fin r → K) :
    S.h (∑ i, t i • b i) y = ∑ i, S.c (t i) * S.h (b i) y := by sorry
