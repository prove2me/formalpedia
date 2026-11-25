-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_minimalPrime_add_one_of_fintype_a79e001126b8
-- name    : P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_minimalPrime_add_one_of_fintype_a79e001126b8
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:53:14.681071+00:00
-- url     : https://prove2.me/theorems/0a0cca0a-f5c7-4d47-98cf-a29e923a7d78
-- title:
--   P2 M Ground Theory Heights  Heights ring Krull Dim quotient minimal Prime add one of fintype a79e001126b8: P2 M Ground Theory Heights  Heights ring Krull Dim quotient minimal Prime add one of fintype
-- statement:
--   The P2 M Ground Theory Heights  Heights ring Krull Dim quotient minimal Prime add one of fintype a79e001126b8 construction uses the P2 M Ground Theory Heights  Heights ring Krull Dim quotient minimal Prime add one of fintype a79e001126b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalModelGoodPointGeneric.lean#L15-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalModelGoodPointGeneric.lean#L15-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelGoodPointGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCodimOneUniformiser
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProjectionUnramifiedGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelOpenMapping
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RingKrullDimQuotientMinimalPrimeAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelGoodPointGeneric
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
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_minimalPrime_add_one_of_fintype_a79e001126b8 {σ : Type} [Fintype σ]
    {V W : Ideal (MvPolynomial σ ℂ)} [hVp : V.IsPrime]
    {f : MvPolynomial σ ℂ} (hf : f ∉ V) (hW : W ∈ (V ⊔ Ideal.span {f}).minimalPrimes)
    (hfin : ringKrullDim (MvPolynomial σ ℂ ⧸ V) ≠ ⊤) :
    ringKrullDim (MvPolynomial σ ℂ ⧸ W) + 1 = ringKrullDim (MvPolynomial σ ℂ ⧸ V) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ringKrullDim_quotient_minimalPrime_add_one_of_fintype» := P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_minimalPrime_add_one_of_fintype_a79e001126b8
