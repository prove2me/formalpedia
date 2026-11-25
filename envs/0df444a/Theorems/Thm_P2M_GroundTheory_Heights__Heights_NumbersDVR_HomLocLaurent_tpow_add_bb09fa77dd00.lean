-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_tpow_add_bb09fa77dd00
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_tpow_add_bb09fa77dd00
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:29:50.176391+00:00
-- url     : https://prove2.me/theorems/bf3522c2-1d63-4cdc-b000-1d37dfc4bf04
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent tpow add bb09fa77dd00: P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent tpow add bb09fa77dd00
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent tpow add bb09fa77dd00 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent tpow add bb09fa77dd00 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleHomLocLaurent.lean#L108-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleHomLocLaurent.lean#L108-L109

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
variable [Fintype K] (P W : Ideal (MRing ι R)) [P.IsPrime] [W.IsPrime] (T : ∀ k, ι k)

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_tpow_add_bb09fa77dd00 (m n : K → ℕ) : (tpow T (m + n) : MRing ι R) = tpow T m * tpow T n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«HomLocLaurent».«tpow_add» := P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_tpow_add_bb09fa77dd00
