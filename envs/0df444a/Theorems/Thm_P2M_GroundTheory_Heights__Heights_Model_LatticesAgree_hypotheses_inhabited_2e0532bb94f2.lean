-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_LatticesAgree_hypotheses_inhabited_2e0532bb94f2
-- name    : P2M_GroundTheory_Heights__Heights_Model_LatticesAgree_hypotheses_inhabited_2e0532bb94f2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:00.993961+00:00
-- url     : https://prove2.me/theorems/a60bc356-2e3a-4fec-be9b-4dfa2beb0c57
-- title:
--   P2 M Ground Theory Heights  Heights Model Lattices Agree hypotheses inhabited 2e0532bb94f2: P2 M Ground Theory Heights  Heights Model Lattices Agree hypotheses inhabited 2e0532bb94f2
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Lattices Agree hypotheses inhabited 2e0532bb94f2 construction uses the P2 M Ground Theory Heights  Heights Model Lattices Agree hypotheses inhabited 2e0532bb94f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L489-L499
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L489-L499

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
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
open NumbersDVR ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_Model_LatticesAgree_hypotheses_inhabited_2e0532bb94f2 :
    Module.Finite ℤ (Submodule.span ℤ {(1 : ℚ)}) ∧
      Module.Projective ℤ (Submodule.span ℤ {(1 : ℚ)}) ∧
      Submodule.span ℚ ((Submodule.span ℤ {(1 : ℚ)} : Submodule ℤ ℚ) : Set ℚ) = ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«LatticesAgree».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_Model_LatticesAgree_hypotheses_inhabited_2e0532bb94f2
