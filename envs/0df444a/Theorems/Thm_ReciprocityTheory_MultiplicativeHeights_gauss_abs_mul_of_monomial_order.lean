-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_abs_mul_of_monomial_order
-- name    : ReciprocityTheory.MultiplicativeHeights.gauss_abs_mul_of_monomial_order
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:14.095227+00:00
-- url     : https://prove2.me/theorems/2d1e1086-fbde-4153-972c-6c12047aea02
-- title:
--   Multiplicative Heights: gauss abs mul of monomial order
-- statement:
--   The Multiplicative Heights construction uses the gauss abs mul of monomial order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussAbsMulOfMonomialOrder.lean#L69-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussAbsMulOfMonomialOrder.lean#L69-L141

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

theorem ReciprocityTheory.MultiplicativeHeights.gauss_abs_mul_of_monomial_order (m : MonomialOrder σ) (w : FinitePlace K)
    (f g : MvPolynomial σ K) (hf : f ≠ 0) (hg : g ≠ 0) :
    gaussAbs w (f * g) = gaussAbs w f * gaussAbs w g := by sorry
