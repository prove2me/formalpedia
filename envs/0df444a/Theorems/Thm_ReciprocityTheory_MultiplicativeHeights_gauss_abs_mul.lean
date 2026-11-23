-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_abs_mul
-- name    : ReciprocityTheory.MultiplicativeHeights.gauss_abs_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:06.103283+00:00
-- url     : https://prove2.me/theorems/54687814-484e-423d-98f5-b57c39e280eb
-- title:
--   Multiplicative Heights: gauss abs mul
-- statement:
--   The Multiplicative Heights construction uses the gauss abs mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussAbsMulOfMonomialOrder.lean#L143-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussAbsMulOfMonomialOrder.lean#L143-L148

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

theorem ReciprocityTheory.MultiplicativeHeights.gauss_abs_mul [Fintype σ] (w : FinitePlace K)
    (f g : MvPolynomial σ K) (hf : f ≠ 0) (hg : g ≠ 0) :
    gaussAbs w (f * g) = gaussAbs w f * gaussAbs w g := by sorry
