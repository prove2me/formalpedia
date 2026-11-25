-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_isVectorBundle_freeModule_ea3cf8102b36
-- name    : P2M_GroundTheory_Heights__Heights_Model_isVectorBundle_freeModule_ea3cf8102b36
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:32:08.577569+00:00
-- url     : https://prove2.me/theorems/7ef656bc-41bf-43c7-a538-ebacaf7fb0e1
-- title:
--   P2 M Ground Theory Heights  Heights Model is Vector Bundle free Module ea3cf8102b36: P2 M Ground Theory Heights  Heights Model is Vector Bundle free Module ea3cf8102b36
-- statement:
--   The P2 M Ground Theory Heights  Heights Model is Vector Bundle free Module ea3cf8102b36 construction uses the P2 M Ground Theory Heights  Heights Model is Vector Bundle free Module ea3cf8102b36 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSpreadLocal.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSpreadLocal.lean#L15-L20

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

theorem P2M_GroundTheory_Heights__Heights_Model_isVectorBundle_freeModule_ea3cf8102b36 (h : FreeSheafBasis.Statement.{u}) (Y : Scheme.{u}) (n : ℕ) :
    IsVectorBundle (freeModule Y n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«isVectorBundle_freeModule» := P2M_GroundTheory_Heights__Heights_Model_isVectorBundle_freeModule_ea3cf8102b36
