-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_gram_nonneg_03110800f026
-- name    : P2M_GroundTheory_Heights__Heights_det_gram_nonneg_03110800f026
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:54.851619+00:00
-- url     : https://prove2.me/theorems/4105db0d-3fff-4b6d-9a04-d30be5e1a5bb
-- title:
--   P2 M Ground Theory Heights  Heights det gram nonneg 03110800f026: P2 M Ground Theory Heights  Heights det gram nonneg 03110800f026
-- statement:
--   The P2 M Ground Theory Heights  Heights det gram nonneg 03110800f026 construction uses the P2 M Ground Theory Heights  Heights det gram nonneg 03110800f026 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Extension.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Extension.lean#L76-L78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
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
open Matrix
open scoped ComplexOrder
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem P2M_GroundTheory_Heights__Heights_det_gram_nonneg_03110800f026 {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → V) :
    0 ≤ det (gram ℂ w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«det_gram_nonneg» := P2M_GroundTheory_Heights__Heights_det_gram_nonneg_03110800f026
