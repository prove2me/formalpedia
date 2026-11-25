-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_quot_mem_6be65faba13b
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_quot_mem_6be65faba13b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:06:25.668795+00:00
-- url     : https://prove2.me/theorems/d51f4ddd-7399-4584-9c46-b415784458e9
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Noetherian quot mem 6be65faba13b: P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Noetherian quot mem 6be65faba13b
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Noetherian quot mem 6be65faba13b construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Noetherian quot mem 6be65faba13b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingNoetherian.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingNoetherian.lean#L56-L58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingNoetherian
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
open GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingNoetherian
variable {R : Type u} [CommRing R] {K : Type} [DecidableEq K] {ι : K → Type}
variable (P : Ideal (MRing ι R)) [P.IsPrime]
variable {P}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_quot_mem_6be65faba13b {W : Ideal (MRing ι R)} {b : K → ℕ} {f g : MRing ι R} (hf : IsMultiHomog f b)
    (hg : IsMultiHomog g b) (hgW : g ∉ W) : img P f / img P g ∈ homLocRing P W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«HomLocRingNoetherian».«quot_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_quot_mem_6be65faba13b
