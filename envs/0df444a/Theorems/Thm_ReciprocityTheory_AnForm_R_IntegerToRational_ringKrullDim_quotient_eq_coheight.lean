-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_ringKrullDim_quotient_eq_coheight
-- name    : ReciprocityTheory.AnForm.R.IntegerToRational.ringKrullDim_quotient_eq_coheight
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:51.74472+00:00
-- url     : https://prove2.me/theorems/e0181777-3c38-43f8-93df-b64e3722eb23
-- title:
--   Integer To Rational: ring Krull Dim quotient eq coheight
-- statement:
--   The Integer To Rational construction uses the ring Krull Dim quotient eq coheight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IntToRatA.lean#L68-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IntToRatA.lean#L68-L73

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

theorem ReciprocityTheory.AnForm.R.IntegerToRational.ringKrullDim_quotient_eq_coheight {A : Type*} [CommRing A] (I : Ideal A) [hI : I.IsPrime] :
    ringKrullDim (A ⧸ I) = (Order.coheight (⟨I, hI⟩ : PrimeSpectrum A) : WithBot ℕ∞) := by sorry
