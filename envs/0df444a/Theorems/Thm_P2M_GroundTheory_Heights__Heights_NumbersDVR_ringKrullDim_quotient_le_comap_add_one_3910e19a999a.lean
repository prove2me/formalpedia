-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ringKrullDim_quotient_le_comap_add_one_3910e19a999a
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_ringKrullDim_quotient_le_comap_add_one_3910e19a999a
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:12:32.414804+00:00
-- url     : https://prove2.me/theorems/c8dad2f1-d89f-4174-83ec-797d07ab8023
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR ring Krull Dim quotient le comap add one 3910e19a999a: P2 M Ground Theory Heights  Heights Numbers DVR ring Krull Dim quotient le comap add one 3910e19a
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR ring Krull Dim quotient le comap add one 3910e19a999a construction uses the P2 M Ground Theory Heights  Heights Numbers DVR ring Krull Dim quotient le comap add one 3910e19a999a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/RingKrullDimQuotientLeComapAddOne.lean#L10-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/RingKrullDimQuotientLeComapAddOne.lean#L10-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimStrictDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_RingKrullDimQuotientLeComapAddOne
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_ringKrullDim_quotient_le_comap_add_one_3910e19a999a {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {J : Type} {R : Type*} [CommRing R] [IsNoetherianRing R]
    (G' : Ideal (MRing (extIdx ι J) R)) [G'.IsPrime] (j₀ : J)
    (hY : ∀ j, j ≠ j₀ → (newVar j : MRing (extIdx ι J) R) ∈ G') :
    ringKrullDim (MRing (extIdx ι J) R ⧸ G') ≤
      ringKrullDim (MRing ι R ⧸ G'.comap (liftForm (J := J) (ι := ι) (R := R))) + 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«ringKrullDim_quotient_le_comap_add_one» := P2M_GroundTheory_Heights__Heights_NumbersDVR_ringKrullDim_quotient_le_comap_add_one_3910e19a999a
