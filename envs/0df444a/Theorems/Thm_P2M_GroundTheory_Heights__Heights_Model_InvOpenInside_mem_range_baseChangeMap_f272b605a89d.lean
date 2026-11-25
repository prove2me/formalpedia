-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_InvOpenInside_mem_range_baseChangeMap_f272b605a89d
-- name    : P2M_GroundTheory_Heights__Heights_Model_InvOpenInside_mem_range_baseChangeMap_f272b605a89d
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:48.521808+00:00
-- url     : https://prove2.me/theorems/f155dfe5-2558-46bf-b65c-aa4f670ca481
-- title:
--   P2 M Ground Theory Heights  Heights Model Inv Open Inside mem range base Change Map f272b605a89d: P2 M Ground Theory Heights  Heights Model Inv Open Inside mem range base Change Map f272b605a89d
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Inv Open Inside mem range base Change Map f272b605a89d construction uses the P2 M Ground Theory Heights  Heights Model Inv Open Inside mem range base Change Map f272b605a89d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PInvOpenInside.lean#L14-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PInvOpenInside.lean#L14-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsInvOpenInside
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PInvOpenInside
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
open GroundTheory.Heights₂.Heights.Model.InvOpenInside

theorem P2M_GroundTheory_Heights__Heights_Model_InvOpenInside_mem_range_baseChangeMap_f272b605a89d {X : Scheme.{0}} (f : X ⟶ SpecZ) (p : Nat.Primes) (x : X)
    (hx : Disjoint ((Ideal.span {((p : ℕ) : ℤ)}).primeCompl : Set ℤ) (f.base x).asIdeal) :
    x ∈ Set.range (baseChangeMap f (ZLoc p)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«InvOpenInside».«mem_range_baseChangeMap» := P2M_GroundTheory_Heights__Heights_Model_InvOpenInside_mem_range_baseChangeMap_f272b605a89d
