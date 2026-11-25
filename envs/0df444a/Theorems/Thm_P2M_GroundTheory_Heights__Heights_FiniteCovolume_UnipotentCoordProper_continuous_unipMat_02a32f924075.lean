-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCoordProper_continuous_unipMat_02a32f924075
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCoordProper_continuous_unipMat_02a32f924075
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:55:39.986263+00:00
-- url     : https://prove2.me/theorems/33799dd9-486f-4d05-91a0-88c28ecc750b
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Coord Proper continuous unip Mat 02a32f924075: P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Coord Proper continuous unip
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Coord Proper continuous unip Mat 02a32f924075 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Coord Proper continuous unip Mat 02a32f924075 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentCoordProper.lean#L22-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentCoordProper.lean#L22-L30

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipotentCoordProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentCoordProper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.UnipotentCoordProper
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCoordProper_continuous_unipMat_02a32f924075 (H : Matrix ι ι ℂ) (X W₀ : ι → ℂ) :
    Continuous (unipMat H X W₀) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«UnipotentCoordProper».«continuous_unipMat» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCoordProper_continuous_unipMat_02a32f924075
