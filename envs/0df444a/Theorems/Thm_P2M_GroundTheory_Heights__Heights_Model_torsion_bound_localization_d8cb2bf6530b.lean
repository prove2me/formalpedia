-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_torsion_bound_localization_d8cb2bf6530b
-- name    : P2M_GroundTheory_Heights__Heights_Model_torsion_bound_localization_d8cb2bf6530b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:58.12554+00:00
-- url     : https://prove2.me/theorems/6269cec8-d022-432c-9b52-9043e7366a63
-- title:
--   P2 M Ground Theory Heights  Heights Model torsion bound localization d8cb2bf6530b: P2 M Ground Theory Heights  Heights Model torsion bound localization d8cb2bf6530b
-- statement:
--   The P2 M Ground Theory Heights  Heights Model torsion bound localization d8cb2bf6530b construction uses the P2 M Ground Theory Heights  Heights Model torsion bound localization d8cb2bf6530b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGenericSections.lean#L34-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGenericSections.lean#L34-L48

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

theorem P2M_GroundTheory_Heights__Heights_Model_torsion_bound_localization_d8cb2bf6530b {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (S : Submonoid A) [IsLocalization S B] {N : ℕ}
    (hN : ∀ (n : ℤ) (a : A), n ≠ 0 → (n : A) * a = 0 → (N : A) * a = 0)
    (n : ℤ) (b : B) (hn : n ≠ 0) (hb : (n : B) * b = 0) : (N : B) * b = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«torsion_bound_localization» := P2M_GroundTheory_Heights__Heights_Model_torsion_bound_localization_d8cb2bf6530b
