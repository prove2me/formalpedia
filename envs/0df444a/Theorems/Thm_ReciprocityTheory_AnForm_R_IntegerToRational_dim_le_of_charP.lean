-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_dim_le_of_charP
-- name    : ReciprocityTheory.AnForm.R.IntegerToRational.dim_le_of_charP
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:04:47.624092+00:00
-- url     : https://prove2.me/theorems/09c0cc7b-19f6-4299-8123-0ae49ec5d9ea
-- title:
--   Integer To Rational: dim le of char P
-- statement:
--   The Integer To Rational construction uses the dim le of char P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IntToRatA.lean#L112-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IntToRatA.lean#L112-L201

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

theorem ReciprocityTheory.AnForm.R.IntegerToRational.dim_le_of_charP (q q' : Ideal (MvPolynomial σ ℤ)) [q.IsPrime] [q'.IsPrime] (hle : q ≤ q')
    (hq : ChZero q) (hq' : ¬ ChZero q') :
    ringKrullDim (MvPolynomial σ ℤ ⧸ q') ≤
      ringKrullDim (MvPolynomial σ ℚ ⧸ Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) q) := by sorry
