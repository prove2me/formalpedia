-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_eq_zero_of_aeval_mem
-- name    : ReciprocityTheory.AnForm.R.IntegerToRational.eq_zero_of_aeval_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:51:37.523446+00:00
-- url     : https://prove2.me/theorems/2fdd9320-6f03-48d8-bdcd-1bdb57e10bdd
-- title:
--   Integer To Rational: eq zero of aeval mem
-- statement:
--   The Integer To Rational construction uses the eq zero of aeval mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IntToRatA.lean#L75-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IntToRatA.lean#L75-L110

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

theorem ReciprocityTheory.AnForm.R.IntegerToRational.eq_zero_of_aeval_mem {ι : Type*} (q : Ideal (MvPolynomial σ ℤ)) [q.IsPrime] (hq : ChZero q)
    (p : ℕ) (hp : 1 < p) (x : ι → MvPolynomial σ ℤ)
    (hred : ∀ G : MvPolynomial ι ℤ, aeval x G ∈ q → map (Int.castRingHom (ZMod p)) G = 0)
    (G : MvPolynomial ι ℤ) (hG : aeval x G ∈ q) : G = 0 := by sorry
