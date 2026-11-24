-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodPointBranch_consZero_tail_d132be48cbd8
-- name    : P2M_GroundTheory_Heights__Heights_GoodPointBranch_consZero_tail_d132be48cbd8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:17.574662+00:00
-- url     : https://prove2.me/theorems/dc3f79dd-8c9f-4e7e-adad-4468079de3d0
-- title:
--   P2 M Ground Theory Heights  Heights Good Point Branch cons Zero tail d132be48cbd8: P2 M Ground Theory Heights  Heights Good Point Branch cons Zero tail d132be48cbd8
-- statement:
--   The P2 M Ground Theory Heights  Heights Good Point Branch cons Zero tail d132be48cbd8 construction uses the P2 M Ground Theory Heights  Heights Good Point Branch cons Zero tail d132be48cbd8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GoodPointBranchSlice.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GoodPointBranchSlice.lean#L27-L29

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

theorem P2M_GroundTheory_Heights__Heights_GoodPointBranch_consZero_tail_d132be48cbd8 {d : ℕ} (t : Fin (d + 1) → ℂ) (ht : t 0 = 0) : consZero d (Fin.tail t) = t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GoodPointBranch».«consZero_tail» := P2M_GroundTheory_Heights__Heights_GoodPointBranch_consZero_tail_d132be48cbd8
