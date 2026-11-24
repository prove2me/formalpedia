-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_map_residue_weightedHomogeneousComponent_b0c16ffbf749
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_map_residue_weightedHomogeneousComponent_b0c16ffbf749
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:02.419454+00:00
-- url     : https://prove2.me/theorems/a4bf427b-52a1-496f-aafb-a141e08c298a
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR map residue weighted Homogeneous Component b0c16ffbf749: P2 M Ground Theory Heights  Heights Numbers DVR map residue weighted Homogeneous Component b0c1
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR map residue weighted Homogeneous Component b0c16ffbf749 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR map residue weighted Homogeneous Component b0c16ffbf749 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSpecialPieceRank.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSpecialPieceRank.lean#L18-L24

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_map_residue_weightedHomogeneousComponent_b0c16ffbf749 (m : K → ℕ) (f : MRing ι O) :
    MvPolynomial.map (IsLocalRing.residue O) (weightedHomogeneousComponent (blockWeight ι) m f) =
      weightedHomogeneousComponent (blockWeight ι) m (MvPolynomial.map (IsLocalRing.residue O) f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«map_residue_weightedHomogeneousComponent» := P2M_GroundTheory_Heights__Heights_NumbersDVR_map_residue_weightedHomogeneousComponent_b0c16ffbf749
