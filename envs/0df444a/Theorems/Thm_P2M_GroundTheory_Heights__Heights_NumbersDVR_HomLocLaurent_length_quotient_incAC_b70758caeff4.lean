-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_length_quotient_incAC_b70758caeff4
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_length_quotient_incAC_b70758caeff4
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:32:16.819818+00:00
-- url     : https://prove2.me/theorems/0c908872-0b82-4fd5-84e2-718904ee5698
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent length quotient inc AC b70758caeff4: P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent length quotient inc AC b70758caeff4
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent length quotient inc AC b70758caeff4 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent length quotient inc AC b70758caeff4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleHomLocLaurent.lean#L529-L551
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleHomLocLaurent.lean#L529-L551

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
  (T : ∀ k, ι k) (hPW : P ≤ W) (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι R) ∉ W)
include hT

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_length_quotient_incAC_b70758caeff4 (hPh : IsMultiHomogIdeal P) (hWh : IsMultiHomogIdeal W)
    [IsLocalRing (homLocRing P W)] (a : homLocRing P W) :
    Module.length (locC hPW) (locC hPW ⧸ Ideal.span {incAC hPW a}) =
      Module.length (homLocRing P W) (homLocRing P W ⧸ Ideal.span {a}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«HomLocLaurent».«length_quotient_incAC» := P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_length_quotient_incAC_b70758caeff4
