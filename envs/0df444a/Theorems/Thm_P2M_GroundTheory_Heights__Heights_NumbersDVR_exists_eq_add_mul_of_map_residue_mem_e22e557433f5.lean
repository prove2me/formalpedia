-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_eq_add_mul_of_map_residue_mem_e22e557433f5
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_eq_add_mul_of_map_residue_mem_e22e557433f5
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:09:57.136616+00:00
-- url     : https://prove2.me/theorems/d7dddab2-ccca-410c-92bf-3b1e2a6c50e7
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR exists eq add mul of map residue mem e22e557433f5: P2 M Ground Theory Heights  Heights Numbers DVR exists eq add mul of map residue mem e22e557433f5
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR exists eq add mul of map residue mem e22e557433f5 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR exists eq add mul of map residue mem e22e557433f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSpecialPieceRank.lean#L45-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSpecialPieceRank.lean#L45-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialPieceRank
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
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_eq_add_mul_of_map_residue_mem_e22e557433f5 {ϖ : O} (hϖ : Irreducible ϖ) {P : Ideal (MRing ι O)}
    (hP : IsMultiHomogIdeal P) {m : K → ℕ} {f : MRing ι O}
    (hf : f ∈ weightedHomogeneousSubmodule O (blockWeight ι) m)
    (hfP : MvPolynomial.map (IsLocalRing.residue O) f ∈ specialIdeal P) :
    ∃ p ∈ P, ∃ g ∈ weightedHomogeneousSubmodule O (blockWeight ι) m, f = p + C ϖ * g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«exists_eq_add_mul_of_map_residue_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_eq_add_mul_of_map_residue_mem_e22e557433f5
