-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_map_maximalIdeal_incAC_0e098a0654dc
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_map_maximalIdeal_incAC_0e098a0654dc
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:31:34.30478+00:00
-- url     : https://prove2.me/theorems/960c1a2e-e8b8-4335-bed0-560211269af5
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent map maximal Ideal inc AC 0e098a0654dc: P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent map maximal Ideal inc AC 0e098a06
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent map maximal Ideal inc AC 0e098a0654dc construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent map maximal Ideal inc AC 0e098a0654dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleHomLocLaurent.lean#L434-L483
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleHomLocLaurent.lean#L434-L483

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpFibreDegreeCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleHomLocLaurent
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
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
open GroundTheory.Heights₂.Heights.NumbersDVR.HomLocLaurent
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
variable [Fintype K] {P W : Ideal (MRing ι R)} [P.IsPrime] [W.IsPrime]
variable (T : ∀ k, ι k) (hPW : P ≤ W) (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι R) ∉ W)
include hT

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_map_maximalIdeal_incAC_0e098a0654dc [IsLocalRing (homLocRing P W)] (hWh : IsMultiHomogIdeal W) :
    letI := (algQC hPW).toAlgebra
    haveI := wbar_isPrime hPW
    haveI := locC_isLocalization hPW
    haveI := IsLocalization.AtPrime.isLocalRing (locC hPW) (W.map (Ideal.Quotient.mk P))
    (IsLocalRing.maximalIdeal (homLocRing P W)).map (incAC hPW) =
      IsLocalRing.maximalIdeal (locC hPW) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«HomLocLaurent».«map_maximalIdeal_incAC» := P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_map_maximalIdeal_incAC_0e098a0654dc
