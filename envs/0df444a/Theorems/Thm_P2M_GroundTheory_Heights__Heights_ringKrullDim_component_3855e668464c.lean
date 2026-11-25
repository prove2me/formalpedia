-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_component_3855e668464c
-- name    : P2M_GroundTheory_Heights__Heights_ringKrullDim_component_3855e668464c
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:19:19.133496+00:00
-- url     : https://prove2.me/theorems/31d04c0c-159d-4a0a-909f-5b99735f1ab2
-- title:
--   P2 M Ground Theory Heights  Heights ring Krull Dim component 3855e668464c: P2 M Ground Theory Heights  Heights ring Krull Dim component 3855e668464c
-- statement:
--   The P2 M Ground Theory Heights  Heights ring Krull Dim component 3855e668464c construction uses the P2 M Ground Theory Heights  Heights ring Krull Dim component 3855e668464c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceMultGeneral.lean#L33-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceMultGeneral.lean#L33-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceMultGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMGeneralPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseSliceGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthTransverseSlice
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceMultGeneral
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
open MvPolynomial Matrix ComplexSets

theorem P2M_GroundTheory_Heights__Heights_ringKrullDim_component_3855e668464c {n d : ℕ} {J W : Ideal (MvPolynomial (Fin n) ℂ)} [J.IsPrime]
    {s : MvPolynomial (Fin n) ℂ} (hs : s ∉ J) (hW : W ∈ (J ⊔ Ideal.span {s}).minimalPrimes)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((d + 1 : ℕ) : WithBot ℕ∞)) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = ((d : ℕ) : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ringKrullDim_component» := P2M_GroundTheory_Heights__Heights_ringKrullDim_component_3855e668464c
