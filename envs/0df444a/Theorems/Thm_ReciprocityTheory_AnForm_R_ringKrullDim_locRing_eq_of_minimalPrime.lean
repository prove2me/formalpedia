-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_ringKrullDim_locRing_eq_of_minimalPrime
-- name    : ReciprocityTheory.AnForm.R.ringKrullDim_locRing_eq_of_minimalPrime
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:38:48.495815+00:00
-- url     : https://prove2.me/theorems/31c1c692-fa22-5f9d-9453-3ad8fbf9c5e8
-- title:
--   R: ring Krull Dim loc Ring eq of minimal Prime
-- statement:
--   The R construction uses the ring Krull Dim loc Ring eq of minimal Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/RingKrullDimLocRingEqOfMinimalPrime.lean#L107-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/RingKrullDimLocRingEqOfMinimalPrime.lean#L107-L117

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_RingKrullDimLocRingEqOfMinimalPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
variable {n : ℕ}

theorem ReciprocityTheory.AnForm.R.ringKrullDim_locRing_eq_of_minimalPrime (K : Ideal (MvPolynomial (Fin n) ℂ))
    (p p' : Fin n → ℂ) [IsRegularLocalRing (locRing K p)] [IsRegularLocalRing (locRing K p')]
    (𝔮 : Ideal (MvPolynomial (Fin n) ℂ)) (h𝔮 : 𝔮 ∈ K.minimalPrimes)
    (hp : 𝔮 ≤ ptIdeal p) (hp' : 𝔮 ≤ ptIdeal p') :
    ringKrullDim (locRing K p) = ringKrullDim (locRing K p') := by sorry
