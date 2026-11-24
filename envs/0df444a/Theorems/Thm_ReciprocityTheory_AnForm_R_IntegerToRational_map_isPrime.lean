-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_map_isPrime
-- name    : ReciprocityTheory.AnForm.R.IntegerToRational.map_isPrime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:06.675907+00:00
-- url     : https://prove2.me/theorems/fcfd9917-3ae7-491b-9190-0f7d0a42c0ce
-- title:
--   Integer To Rational: map is Prime
-- statement:
--   The Integer To Rational construction uses the map is Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IntToRatA.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IntToRatA.lean#L22-L27

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

theorem ReciprocityTheory.AnForm.R.IntegerToRational.map_isPrime (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime] (hP : ChZero P) :
    (Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) P).IsPrime := by sorry
