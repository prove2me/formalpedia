-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_eq_zero_of_intCast_mul_eq_zero_44d637363897
-- name    : P2M_GroundTheory_Heights__Heights_Model_eq_zero_of_intCast_mul_eq_zero_44d637363897
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:30:12.76819+00:00
-- url     : https://prove2.me/theorems/7360e739-5719-4f4c-b317-cdb2647da03a
-- title:
--   P2 M Ground Theory Heights  Heights Model eq zero of int Cast mul eq zero 44d637363897: P2 M Ground Theory Heights  Heights Model eq zero of int Cast mul eq zero 44d637363897
-- statement:
--   The P2 M Ground Theory Heights  Heights Model eq zero of int Cast mul eq zero 44d637363897 construction uses the P2 M Ground Theory Heights  Heights Model eq zero of int Cast mul eq zero 44d637363897 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGenericSections.lean#L69-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGenericSections.lean#L69-L92

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections
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
open CategoryTheory Limits AlgebraicGeometry Opposite
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Model_eq_zero_of_intCast_mul_eq_zero_44d637363897 {X : Scheme.{0}} (f : X ⟶ SpecZ) (k : ℤ)
    (hcov : ∀ x : X, ∃ (U : X.affineOpens) (N : ℕ), x ∈ (U : X.Opens) ∧ (N : ℤ) ∣ k ∧
      ∀ (n : ℤ) (a : Γ(X, U)), n ≠ 0 → (n : Γ(X, U)) * a = 0 → (N : Γ(X, U)) * a = 0)
    {W : X.Opens} (hW : W ≤ invOpen f k) (n : ℤ) (hn : n ≠ 0) (s : Γ(X, W))
    (hs : (n : Γ(X, W)) * s = 0) : s = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«eq_zero_of_intCast_mul_eq_zero» := P2M_GroundTheory_Heights__Heights_Model_eq_zero_of_intCast_mul_eq_zero_44d637363897
