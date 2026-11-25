-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodPointBranch_consCLM_apply_1d763c4552d2
-- name    : P2M_GroundTheory_Heights__Heights_GoodPointBranch_consCLM_apply_1d763c4552d2
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:24:18.753917+00:00
-- url     : https://prove2.me/theorems/e22d331f-ceb8-52f4-9704-cccba5b5c9fc
-- title:
--   P2 M Ground Theory Heights  Heights Good Point Branch cons CLM apply 1d763c4552d2: P2 M Ground Theory Heights  Heights Good Point Branch cons CLM apply 1d763c4552d2
-- statement:
--   The P2 M Ground Theory Heights  Heights Good Point Branch cons CLM apply 1d763c4552d2 construction uses the P2 M Ground Theory Heights  Heights Good Point Branch cons CLM apply 1d763c4552d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GoodPointBranchSlice.lean#L59-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GoodPointBranchSlice.lean#L59-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGoodPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_NormalModelFibreNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GoodPointBranchSlice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Filter Topology Matrix ComplexSets Metric Set
noncomputable section
open GroundTheory.Heights₂.Heights.GoodPointBranch

theorem P2M_GroundTheory_Heights__Heights_GoodPointBranch_consCLM_apply_1d763c4552d2 {d : ℕ} (p : ℂ × (Fin d → ℂ)) : consCLM d p = vecCons p.1 p.2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GoodPointBranch».«consCLM_apply» := P2M_GroundTheory_Heights__Heights_GoodPointBranch_consCLM_apply_1d763c4552d2
