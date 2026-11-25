-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericDimGe_exists_isPrime_between_not_mem_f98685f45555
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericDimGe_exists_isPrime_between_not_mem_f98685f45555
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:07:02.301007+00:00
-- url     : https://prove2.me/theorems/f45190f5-697b-4b77-995f-f73a38f5a3e7
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Generic Dim Ge exists is Prime between not mem f98685f45555: P2 M Ground Theory Heights  Heights Numbers DVR Generic Dim Ge exists is Prime between not
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Generic Dim Ge exists is Prime between not mem f98685f45555 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Generic Dim Ge exists is Prime between not mem f98685f45555 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericDimGe.lean#L45-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericDimGe.lean#L45-L100

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericDimGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericDimGe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericDimGe
variable {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericDimGe_exists_isPrime_between_not_mem_f98685f45555 [IsNoetherianRing R] {p q r : Ideal R} [p.IsPrime]
    [q.IsPrime] [r.IsPrime] (hpq : p < q) (hqr : q < r) {x : R} (hx : x ∉ p) :
    ∃ q' : Ideal R, q'.IsPrime ∧ p < q' ∧ q' < r ∧ x ∉ q' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«GenericDimGe».«exists_isPrime_between_not_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericDimGe_exists_isPrime_between_not_mem_f98685f45555
