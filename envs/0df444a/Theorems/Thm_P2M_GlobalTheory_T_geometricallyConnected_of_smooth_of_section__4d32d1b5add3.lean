-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_geometricallyConnected_of_smooth_of_section__4d32d1b5add3
-- name    : P2M_GlobalTheory_T_geometricallyConnected_of_smooth_of_section__4d32d1b5add3
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:10:30.146743+00:00
-- url     : https://prove2.me/theorems/69e4cc5e-583b-428e-9802-bbf946c9e06d
-- title:
--   P2 M Global Theory T geometrically Connected of smooth of section  4d32d1b5add3: P2 M Global Theory T geometrically Connected of smooth of section  4d32d1b5add3
-- statement:
--   The P2 M Global Theory T geometrically Connected of smooth of section  4d32d1b5add3 construction uses the P2 M Global Theory T geometrically Connected of smooth of section  4d32d1b5add3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GeometricallyConnectedOfSmoothOfSectionStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GeometricallyConnectedOfSmoothOfSectionStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GeometricallyConnectedOfSmoothOfSection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GeometricallyConnectedOfSmoothOfSectionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_geometricallyConnected_of_smooth_of_section__4d32d1b5add3 : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)) (e : Spec (CommRingCat.of k) ⟶ X), Smooth f → e ≫ f = 𝟙 _ → ConnectedSpace X → GeometricallyConnected f := by sorry

alias «GlobalTheory».«T».«geometricallyConnected_of_smooth_of_section'» := P2M_GlobalTheory_T_geometricallyConnected_of_smooth_of_section__4d32d1b5add3
