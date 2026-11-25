-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_frac_one_e27c519d0e78
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_frac_one_e27c519d0e78
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:30:11.834645+00:00
-- url     : https://prove2.me/theorems/98af64e5-2e7f-4642-895e-160e69738b72
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Dim Le frac one e27c519d0e78: P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Dim Le frac one e27c519d0e78
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Dim Le frac one e27c519d0e78 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Dim Le frac one e27c519d0e78 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingDimLe.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingDimLe.lean#L25-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultiHomogPrimeCriterion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingDimLe
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
open GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingDimLe
variable {R : Type u} [CommRing R] {K : Type} [DecidableEq K] {ι : K → Type}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_frac_one_e27c519d0e78 (P : Ideal (MRing ι R)) [P.IsPrime] : frac P 1 = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«HomLocRingDimLe».«frac_one» := P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_frac_one_e27c519d0e78
