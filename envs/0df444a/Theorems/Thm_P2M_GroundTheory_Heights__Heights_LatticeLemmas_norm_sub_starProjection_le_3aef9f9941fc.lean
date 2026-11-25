-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_norm_sub_starProjection_le_3aef9f9941fc
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_norm_sub_starProjection_le_3aef9f9941fc
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:35:35.524216+00:00
-- url     : https://prove2.me/theorems/4c55f593-5a16-5fcb-bcfd-40d5ab9f36f8
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas norm sub star Projection le 3aef9f9941fc: P2 M Ground Theory Heights  Heights Lattice Lemmas norm sub star Projection le 3aef9f9941fc
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas norm sub star Projection le 3aef9f9941fc construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas norm sub star Projection le 3aef9f9941fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHadamardMean.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHadamardMean.lean#L16-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PHadamardMean
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField Matrix GroundTheory.Heights₂.Heights
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_norm_sub_starProjection_le_3aef9f9941fc {ι : Type*} [Fintype ι] (v : ι → V) (y : V) :
    ‖y - (Submodule.span ℂ (Set.range v)).starProjection y‖ ≤ ‖y‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«norm_sub_starProjection_le» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_norm_sub_starProjection_le_3aef9f9941fc
