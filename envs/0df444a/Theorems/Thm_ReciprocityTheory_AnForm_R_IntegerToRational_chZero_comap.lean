-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_chZero_comap
-- name    : ReciprocityTheory.AnForm.R.IntegerToRational.chZero_comap
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:51:51.970234+00:00
-- url     : https://prove2.me/theorems/d5d629fe-49cf-4eb3-bdee-36c2919fe1ea
-- title:
--   Integer To Rational: ch Zero comap
-- statement:
--   The Integer To Rational construction uses the ch Zero comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IntToRatA.lean#L37-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IntToRatA.lean#L37-L44

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IntegerToRational
open MvPolynomial
variable {σ : Type} [Fintype σ]
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem ReciprocityTheory.AnForm.R.IntegerToRational.chZero_comap (Q : Ideal (MvPolynomial σ ℚ)) [Q.IsPrime] :
    ChZero (Q.comap (MvPolynomial.map (Int.castRingHom ℚ))) := by sorry
