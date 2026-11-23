-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_sum_right
-- name    : ReciprocityTheory.MultiplicativeHeights.wa_sum_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:48.374804+00:00
-- url     : https://prove2.me/theorems/94e8b4db-7567-4ef6-8631-681bbb61a6e1
-- title:
--   Multiplicative Heights: wa sum right
-- statement:
--   The Multiplicative Heights construction uses the wa sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegAA.lean#L50-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegAA.lean#L50-L54

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

theorem ReciprocityTheory.MultiplicativeHeights.wa_sum_right {K : Type} [Field K] [NumberField K] {r n : ℕ} (S : HermForm K r)
    (x : Fin r → K) (t : Fin n → K) (b : Fin n → Fin r → K) :
    S.h x (∑ i, t i • b i) = ∑ i, t i * S.h x (b i) := by sorry
