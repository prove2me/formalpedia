-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_isLocalization_lau_f48fa42d9057
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_isLocalization_lau_f48fa42d9057
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:31:20.33342+00:00
-- url     : https://prove2.me/theorems/9610cff5-4f88-4d5c-b16e-ce4059c7b150
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent is Localization lau f48fa42d9057: P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent is Localization lau f48fa42d9057
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent is Localization lau f48fa42d9057 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Laurent is Localization lau f48fa42d9057 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleHomLocLaurent.lean#L266-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleHomLocLaurent.lean#L266-L320

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
variable [Fintype K] {P W : Ideal (MRing ι R)} [P.IsPrime] [W.IsPrime] (T : ∀ k, ι k)
  (hPW : P ≤ W) (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι R) ∉ W)

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_isLocalization_lau_f48fa42d9057 (hPh : IsMultiHomogIdeal P) :
    letI := (psiQ T hPW hT hPh).toAlgebra
    IsLocalization (homSub (K := K) P W) (Lau P W) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«HomLocLaurent».«isLocalization_lau» := P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_isLocalization_lau_f48fa42d9057
