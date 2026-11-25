-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_isPreimmersion_baseChangeMap_52e3bc354d38
-- name    : P2M_GroundTheory_Heights__Heights_Model_isPreimmersion_baseChangeMap_52e3bc354d38
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:31:57.016269+00:00
-- url     : https://prove2.me/theorems/83bdbabf-98f8-424a-9a92-112fe76a18e0
-- title:
--   P2 M Ground Theory Heights  Heights Model is Preimmersion base Change Map 52e3bc354d38: P2 M Ground Theory Heights  Heights Model is Preimmersion base Change Map 52e3bc354d38
-- statement:
--   The P2 M Ground Theory Heights  Heights Model is Preimmersion base Change Map 52e3bc354d38 construction uses the P2 M Ground Theory Heights  Heights Model is Preimmersion base Change Map 52e3bc354d38 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSpreadLocal.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSpreadLocal.lean#L22-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsBasisIsoFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSpreadLocal
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
universe u

theorem P2M_GroundTheory_Heights__Heights_Model_isPreimmersion_baseChangeMap_52e3bc354d38 {X : Scheme.{0}} (f : X ⟶ SpecZ) (p : Nat.Primes) :
    IsPreimmersion (baseChangeMap f (ZLoc p)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«isPreimmersion_baseChangeMap» := P2M_GroundTheory_Heights__Heights_Model_isPreimmersion_baseChangeMap_52e3bc354d38
