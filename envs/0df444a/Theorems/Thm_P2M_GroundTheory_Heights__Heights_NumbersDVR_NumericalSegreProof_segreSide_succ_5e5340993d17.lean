-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_segreSide_succ_5e5340993d17
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_segreSide_succ_5e5340993d17
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:08:59.788801+00:00
-- url     : https://prove2.me/theorems/b08232c2-9cd8-497e-a362-bbc7e9f769d0
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof segre Side succ 5e5340993d17: P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof segre Side succ 5e5340993d17
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof segre Side succ 5e5340993d17 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof segre Side succ 5e5340993d17 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PNumericalSegre.lean#L129-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PNumericalSegre.lean#L129-L150

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PNumericalSegre
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegreProof

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_segreSide_succ_5e5340993d17 {K : Type*} [DecidableEq K] {ι : K → Type*} (F : Type*) [Field F]
    (P : Ideal (MRing ι F)) {i : ℕ} (hi : 1 ≤ i) (x : Fin (i + 1) → K → ℤ) (m : ℕ)
    (Y : List (K → ℤ)) :
    segreSide F P x (m + 1) Y =
      segreSide F P (fun j => x (Fin.castSucc j)) m Y +
        segreSide F P x m (x (Fin.last i) :: Y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«NumericalSegreProof».«segreSide_succ» := P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_segreSide_succ_5e5340993d17
