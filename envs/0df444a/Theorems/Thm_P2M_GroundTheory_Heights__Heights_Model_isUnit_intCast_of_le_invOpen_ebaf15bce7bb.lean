-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_isUnit_intCast_of_le_invOpen_ebaf15bce7bb
-- name    : P2M_GroundTheory_Heights__Heights_Model_isUnit_intCast_of_le_invOpen_ebaf15bce7bb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:46.081942+00:00
-- url     : https://prove2.me/theorems/9c26ccc7-90a1-480d-b88b-2b35444641f8
-- title:
--   P2 M Ground Theory Heights  Heights Model is Unit int Cast of le inv Open ebaf15bce7bb: P2 M Ground Theory Heights  Heights Model is Unit int Cast of le inv Open ebaf15bce7bb
-- statement:
--   The P2 M Ground Theory Heights  Heights Model is Unit int Cast of le inv Open ebaf15bce7bb construction uses the P2 M Ground Theory Heights  Heights Model is Unit int Cast of le inv Open ebaf15bce7bb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGenericSections.lean#L60-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGenericSections.lean#L60-L67

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

theorem P2M_GroundTheory_Heights__Heights_Model_isUnit_intCast_of_le_invOpen_ebaf15bce7bb {X : Scheme.{0}} (f : X ⟶ SpecZ) (k : ℤ) {V : X.Opens}
    (hV : V ≤ invOpen f k) : IsUnit (k : Γ(X, V)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«isUnit_intCast_of_le_invOpen» := P2M_GroundTheory_Heights__Heights_Model_isUnit_intCast_of_le_invOpen_ebaf15bce7bb
