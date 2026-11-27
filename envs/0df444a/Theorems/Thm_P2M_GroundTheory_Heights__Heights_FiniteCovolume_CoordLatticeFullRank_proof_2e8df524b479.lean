-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_CoordLatticeFullRank_proof_2e8df524b479
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_CoordLatticeFullRank_proof_2e8df524b479
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:14:09.557683+00:00
-- url     : https://prove2.me/theorems/bd28e3f7-fb35-57a0-963c-243aca7353e6
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Coord Lattice Full Rank proof 2e8df524b479: P2 M Ground Theory Heights  Heights Finite Covolume Coord Lattice Full Rank proof 2e8df524b479
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Coord Lattice Full Rank proof 2e8df524b479 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Coord Lattice Full Rank proof 2e8df524b479 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PCoordLatticeFullRank.lean#L13-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PCoordLatticeFullRank.lean#L13-L62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StCoordLatticeFullRank
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PCoordLatticeFullRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField Module
noncomputable section
variable {E : Type*} [Field E] [NumberField E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_CoordLatticeFullRank_proof_2e8df524b479 (v : Basis ι E W) : CoordLatticeFullRank.Statement v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«CoordLatticeFullRank».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_CoordLatticeFullRank_proof_2e8df524b479
