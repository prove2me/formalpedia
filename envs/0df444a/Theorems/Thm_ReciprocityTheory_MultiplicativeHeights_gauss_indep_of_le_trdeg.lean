-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_indep_of_le_trdeg
-- name    : ReciprocityTheory.MultiplicativeHeights.gauss_indep_of_le_trdeg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:15.463683+00:00
-- url     : https://prove2.me/theorems/da84f200-0ef5-47c7-a970-445dc593e322
-- title:
--   Multiplicative Heights: gauss indep of le trdeg
-- statement:
--   The Multiplicative Heights construction uses the gauss indep of le trdeg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussIndepOfLeTrdeg.lean#L44-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussIndepOfLeTrdeg.lean#L44-L82

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

theorem ReciprocityTheory.MultiplicativeHeights.gauss_indep_of_le_trdeg {E C : Type} [Field E] [Field C] [Algebra E C] {σ : Type}
    [Finite σ] (tb : σ → C)
    (h : Cardinal.mk σ ≤ Algebra.trdeg E (Algebra.adjoin E (Set.range tb))) :
    AlgebraicIndependent E tb := by sorry
