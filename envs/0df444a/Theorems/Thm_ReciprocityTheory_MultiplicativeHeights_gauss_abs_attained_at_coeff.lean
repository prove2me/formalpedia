-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_abs_attained_at_coeff
-- name    : ReciprocityTheory.MultiplicativeHeights.gauss_abs_attained_at_coeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:31.484203+00:00
-- url     : https://prove2.me/theorems/a377a97a-93c9-4d1a-81a2-aeed93d6a64c
-- title:
--   Multiplicative Heights: gauss abs attained at coeff
-- statement:
--   The Multiplicative Heights construction uses the gauss abs attained at coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussAbsMulOfMonomialOrder.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussAbsMulOfMonomialOrder.lean#L30-L36

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_Lemmata_GeneralBFactLeftExtra_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open NumberField
variable {K : Type*} [Field K] [NumberField K] {σ : Type*}

theorem ReciprocityTheory.MultiplicativeHeights.gauss_abs_attained_at_coeff (w : FinitePlace K) (f : MvPolynomial σ K) (hf : f ≠ 0) :
    ∃ s ∈ f.support, gaussAbs w f = w (f.coeff s) := by sorry
