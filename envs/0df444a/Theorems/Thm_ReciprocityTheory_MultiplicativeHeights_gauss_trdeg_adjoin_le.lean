-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_trdeg_adjoin_le
-- name    : ReciprocityTheory.MultiplicativeHeights.gauss_trdeg_adjoin_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:10.16879+00:00
-- url     : https://prove2.me/theorems/7dd75dfd-7b44-4353-a4d4-f2019f680681
-- title:
--   Multiplicative Heights: gauss trdeg adjoin le
-- statement:
--   The Multiplicative Heights construction uses the gauss trdeg adjoin le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussIndepOfLeTrdeg.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussIndepOfLeTrdeg.lean#L22-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussIndepOfLeTrdeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial

theorem ReciprocityTheory.MultiplicativeHeights.gauss_trdeg_adjoin_le {E C : Type} [Field E] [Field C] [Algebra E C] {σ : Type}
    (tb : σ → C) : Algebra.trdeg E (Algebra.adjoin E (Set.range tb)) ≤ Cardinal.mk σ := by sorry
