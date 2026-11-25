-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_map_residue_eq_bed448458014
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_map_residue_eq_bed448458014
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:09:51.420521+00:00
-- url     : https://prove2.me/theorems/f73c5a7f-531e-5d9f-be13-1ce2385345ea
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR exists form map residue eq bed448458014: P2 M Ground Theory Heights  Heights Numbers DVR exists form map residue eq bed448458014
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR exists form map residue eq bed448458014 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR exists form map residue eq bed448458014 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSpecialPieceRank.lean#L34-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSpecialPieceRank.lean#L34-L43

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_map_residue_eq_bed448458014 {m : K → ℕ} {g : MRing ι (IsLocalRing.ResidueField O)}
    (hg : g ∈ weightedHomogeneousSubmodule (IsLocalRing.ResidueField O) (blockWeight ι) m) :
    ∃ f ∈ weightedHomogeneousSubmodule O (blockWeight ι) m,
      MvPolynomial.map (IsLocalRing.residue O) f = g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«exists_form_map_residue_eq» := P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_map_residue_eq_bed448458014
