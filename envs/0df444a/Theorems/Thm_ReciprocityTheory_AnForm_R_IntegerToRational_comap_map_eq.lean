-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_comap_map_eq
-- name    : ReciprocityTheory.AnForm.R.IntegerToRational.comap_map_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:35.881546+00:00
-- url     : https://prove2.me/theorems/8bbf347f-65f0-4cf8-975e-9e9859872ba9
-- title:
--   Integer To Rational: comap map eq
-- statement:
--   The Integer To Rational construction uses the comap map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IntToRatA.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IntToRatA.lean#L29-L35

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

theorem ReciprocityTheory.AnForm.R.IntegerToRational.comap_map_eq (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime] (hP : ChZero P) :
    (Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) P).comap
      (MvPolynomial.map (Int.castRingHom ℚ)) = P := by sorry
