-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueBundles_proof_804af3e711cb
-- name    : P2M_GroundTheory_Heights__Heights_Model_GlueBundles_proof_804af3e711cb
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:31:30.551453+00:00
-- url     : https://prove2.me/theorems/c9a604dd-c9b0-4b2d-ae1d-79fbf24361fc
-- title:
--   P2 M Ground Theory Heights  Heights Model Glue Bundles proof 804af3e711cb: P2 M Ground Theory Heights  Heights Model Glue Bundles proof 804af3e711cb
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Glue Bundles proof 804af3e711cb construction uses the P2 M Ground Theory Heights  Heights Model Glue Bundles proof 804af3e711cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueBundles.lean#L179-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueBundles.lean#L179-L216

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GlueCoherence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueBundles
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
variable {X : Scheme.{0}}

theorem P2M_GroundTheory_Heights__Heights_Model_GlueBundles_proof_804af3e711cb (hSB : SpreadBundle.Statement) (hSI : SpreadIso.Statement)
    (hPC : PrimeOpensCover.Statement) (hGS : GlueModulesStar.Statement)
    (hVR : VectorBundleRestrict.Statement) (hVL : VectorBundleLocal.Statement) :
    GlueBundles.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«GlueBundles».«proof» := P2M_GroundTheory_Heights__Heights_Model_GlueBundles_proof_804af3e711cb
