-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_abs_pos_of_ne_zero
-- name    : ReciprocityTheory.MultiplicativeHeights.gauss_abs_pos_of_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:01.464707+00:00
-- url     : https://prove2.me/theorems/561c42c2-af6e-473e-bffd-fba3c32fac66
-- title:
--   Multiplicative Heights: gauss abs pos of ne zero
-- statement:
--   The Multiplicative Heights construction uses the gauss abs pos of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussAbsMulOfMonomialOrder.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussAbsMulOfMonomialOrder.lean#L38-L42

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

theorem ReciprocityTheory.MultiplicativeHeights.gauss_abs_pos_of_ne_zero (w : FinitePlace K) (f : MvPolynomial σ K) (hf : f ≠ 0) :
    0 < gaussAbs w f := by sorry
