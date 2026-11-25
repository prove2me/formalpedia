-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_minimalPrime_add_one_823c5cc8bf23
-- name    : P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_minimalPrime_add_one_823c5cc8bf23
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:50:34.461528+00:00
-- url     : https://prove2.me/theorems/539f11f5-3e3c-4b9c-abb8-3efd0a23192b
-- title:
--   P2 M Ground Theory Heights  Heights ring Krull Dim quotient minimal Prime add one 823c5cc8bf23: P2 M Ground Theory Heights  Heights ring Krull Dim quotient minimal Prime add one 823c5cc8bf23
-- statement:
--   The P2 M Ground Theory Heights  Heights ring Krull Dim quotient minimal Prime add one 823c5cc8bf23 construction uses the P2 M Ground Theory Heights  Heights ring Krull Dim quotient minimal Prime add one 823c5cc8bf23 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/RingKrullDimQuotientMinimalPrimeAddOne.lean#L35-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/RingKrullDimQuotientMinimalPrimeAddOne.lean#L35-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGoodPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameGraphGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegularOffHypersurface
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RingKrullDimQuotientMinimalPrimeAddOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Filter Topology ComplexSets
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_minimalPrime_add_one_823c5cc8bf23 {n : ℕ} {V W : Ideal (MvPolynomial (Fin n) ℂ)} [hVp : V.IsPrime]
    {f : MvPolynomial (Fin n) ℂ} (hf : f ∉ V) (hW : W ∈ (V ⊔ Ideal.span {f}).minimalPrimes)
    (hfin : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V) ≠ ⊤) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) + 1 = ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ringKrullDim_quotient_minimalPrime_add_one» := P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_minimalPrime_add_one_823c5cc8bf23
