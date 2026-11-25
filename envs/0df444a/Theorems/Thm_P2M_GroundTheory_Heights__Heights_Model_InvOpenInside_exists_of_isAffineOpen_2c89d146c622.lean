-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_InvOpenInside_exists_of_isAffineOpen_2c89d146c622
-- name    : P2M_GroundTheory_Heights__Heights_Model_InvOpenInside_exists_of_isAffineOpen_2c89d146c622
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:30:34.900587+00:00
-- url     : https://prove2.me/theorems/8ef0799c-84f5-4127-9fd7-c0ec12634629
-- title:
--   P2 M Ground Theory Heights  Heights Model Inv Open Inside exists of is Affine Open 2c89d146c622: P2 M Ground Theory Heights  Heights Model Inv Open Inside exists of is Affine Open 2c89d146c622
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Inv Open Inside exists of is Affine Open 2c89d146c622 construction uses the P2 M Ground Theory Heights  Heights Model Inv Open Inside exists of is Affine Open 2c89d146c622 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PInvOpenInside.lean#L28-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PInvOpenInside.lean#L28-L66

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

theorem P2M_GroundTheory_Heights__Heights_Model_InvOpenInside_exists_of_isAffineOpen_2c89d146c622 {X : Scheme.{0}} (f : X ⟶ SpecZ) (p : Nat.Primes) (W : X.Opens)
    (hW : Set.range (baseChangeMap f (ZLoc p)) ⊆ Set.range W.ι) {U : X.Opens}
    (hU : IsAffineOpen U) :
    ∃ s ∈ (Ideal.span {((p : ℕ) : ℤ)}).primeCompl,
      ∀ x ∈ U, x ∉ W → s ∈ (f.base x).asIdeal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«InvOpenInside».«exists_of_isAffineOpen» := P2M_GroundTheory_Heights__Heights_Model_InvOpenInside_exists_of_isAffineOpen_2c89d146c622
