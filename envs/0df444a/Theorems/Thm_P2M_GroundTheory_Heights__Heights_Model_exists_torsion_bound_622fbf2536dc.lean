-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_torsion_bound_622fbf2536dc
-- name    : P2M_GroundTheory_Heights__Heights_Model_exists_torsion_bound_622fbf2536dc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:41.725135+00:00
-- url     : https://prove2.me/theorems/16a23ee2-5ad5-42aa-b5ab-aa9b204b158c
-- title:
--   P2 M Ground Theory Heights  Heights Model exists torsion bound 622fbf2536dc: P2 M Ground Theory Heights  Heights Model exists torsion bound 622fbf2536dc
-- statement:
--   The P2 M Ground Theory Heights  Heights Model exists torsion bound 622fbf2536dc construction uses the P2 M Ground Theory Heights  Heights Model exists torsion bound 622fbf2536dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGenericSections.lean#L12-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGenericSections.lean#L12-L32

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

theorem P2M_GroundTheory_Heights__Heights_Model_exists_torsion_bound_622fbf2536dc (A : Type*) [CommRing A] [IsNoetherianRing A] :
    ∃ N : ℕ, 0 < N ∧ ∀ (n : ℤ) (a : A), n ≠ 0 → (n : A) * a = 0 → (N : A) * a = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«exists_torsion_bound» := P2M_GroundTheory_Heights__Heights_Model_exists_torsion_bound_622fbf2536dc
