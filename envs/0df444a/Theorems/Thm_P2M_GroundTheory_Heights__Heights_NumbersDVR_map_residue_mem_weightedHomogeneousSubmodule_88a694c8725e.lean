-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_map_residue_mem_weightedHomogeneousSubmodule_88a694c8725e
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_map_residue_mem_weightedHomogeneousSubmodule_88a694c8725e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:06.320036+00:00
-- url     : https://prove2.me/theorems/0f25b7ee-45b2-43e5-a88e-15c87554fd8e
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR map residue mem weighted Homogeneous Submodule 88a694c8725e: P2 M Ground Theory Heights  Heights Numbers DVR map residue mem weighted Homogeneous Submod
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR map residue mem weighted Homogeneous Submodule 88a694c8725e construction uses the P2 M Ground Theory Heights  Heights Numbers DVR map residue mem weighted Homogeneous Submodule 88a694c8725e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSpecialPieceRank.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSpecialPieceRank.lean#L26-L32

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_map_residue_mem_weightedHomogeneousSubmodule_88a694c8725e {m : K → ℕ} {f : MRing ι O}
    (hf : f ∈ weightedHomogeneousSubmodule O (blockWeight ι) m) :
    MvPolynomial.map (IsLocalRing.residue O) f ∈
      weightedHomogeneousSubmodule (IsLocalRing.ResidueField O) (blockWeight ι) m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«map_residue_mem_weightedHomogeneousSubmodule» := P2M_GroundTheory_Heights__Heights_NumbersDVR_map_residue_mem_weightedHomogeneousSubmodule_88a694c8725e
