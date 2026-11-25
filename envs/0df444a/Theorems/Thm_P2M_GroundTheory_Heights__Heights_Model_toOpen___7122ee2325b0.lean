-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_toOpen___7122ee2325b0
-- name    : P2M_GroundTheory_Heights__Heights_Model_toOpen___7122ee2325b0
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:49:26.661391+00:00
-- url     : https://prove2.me/theorems/8162db87-0c56-4056-b2a0-e895ae2196c3
-- title:
--   P2 M Ground Theory Heights  Heights Model to Open   7122ee2325b0: P2 M Ground Theory Heights  Heights Model to Open   7122ee2325b0
-- statement:
--   The P2 M Ground Theory Heights  Heights Model to Open   7122ee2325b0 construction uses the P2 M Ground Theory Heights  Heights Model to Open   7122ee2325b0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsSpreadNbhd.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsSpreadNbhd.lean#L18-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadNbhd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
variable {X : Scheme.{0}}

theorem P2M_GroundTheory_Heights__Heights_Model_toOpen___7122ee2325b0 (f : X ⟶ SpecZ) (R : Type) [CommRing R] (W : X.Opens)
    (hW : Set.range (baseChangeMap f R) ⊆ Set.range W.ι) :
    toOpen f R W hW ≫ W.ι = baseChangeMap f R := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«toOpen_ι» := P2M_GroundTheory_Heights__Heights_Model_toOpen___7122ee2325b0
