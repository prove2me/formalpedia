-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GenericPullInj_proof_3c28fd6ff7dc
-- name    : P2M_GroundTheory_Heights__Heights_Model_GenericPullInj_proof_3c28fd6ff7dc
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:31:57.1321+00:00
-- url     : https://prove2.me/theorems/d4998463-2565-479f-a3ef-cb8a3cc32ecc
-- title:
--   P2 M Ground Theory Heights  Heights Model Generic Pull Inj proof 3c28fd6ff7dc: P2 M Ground Theory Heights  Heights Model Generic Pull Inj proof 3c28fd6ff7dc
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Generic Pull Inj proof 3c28fd6ff7dc construction uses the P2 M Ground Theory Heights  Heights Model Generic Pull Inj proof 3c28fd6ff7dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGenericPullInj.lean#L44-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGenericPullInj.lean#L44-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericPullInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericPullInj
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_ClearDenominators_proof_2cf1ed1069ad
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_VectorBundleRestrict_proof_7423c8d31f2c

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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Model_GenericPullInj_proof_3c28fd6ff7dc (h₁ : GenericSectionsInj.Statement)
    (h₂ : PullbackBasis.Statement.{0}) : GenericPullInj.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«GenericPullInj».«proof» := P2M_GroundTheory_Heights__Heights_Model_GenericPullInj_proof_3c28fd6ff7dc
