-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_continuous_unipCoord_2bb02502c78f
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_continuous_unipCoord_2bb02502c78f
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:19:47.755001+00:00
-- url     : https://prove2.me/theorems/1fd339fe-a659-4ccf-af90-acebf0353456
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume continuous unip Coord 2bb02502c78f: P2 M Ground Theory Heights  Heights Finite Covolume continuous unip Coord 2bb02502c78f
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume continuous unip Coord 2bb02502c78f construction uses the P2 M Ground Theory Heights  Heights Finite Covolume continuous unip Coord 2bb02502c78f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StUnipotentCoordProper.lean#L31-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StUnipotentCoordProper.lean#L31-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipotentCoordProper
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
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
  [NumberField E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_continuous_unipCoord_2bb02502c78f (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) :
    Continuous (unipCoord h v x₀ w₀) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«continuous_unipCoord» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_continuous_unipCoord_2bb02502c78f
