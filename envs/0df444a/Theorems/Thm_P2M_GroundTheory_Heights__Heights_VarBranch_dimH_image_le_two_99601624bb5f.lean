-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarBranch_dimH_image_le_two_99601624bb5f
-- name    : P2M_GroundTheory_Heights__Heights_VarBranch_dimH_image_le_two_99601624bb5f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:43:10.027929+00:00
-- url     : https://prove2.me/theorems/8f37d0b5-0705-47e0-9ab7-0c78be80f364
-- title:
--   P2 M Ground Theory Heights  Heights Var Branch dim H image le two 99601624bb5f: P2 M Ground Theory Heights  Heights Var Branch dim H image le two 99601624bb5f
-- statement:
--   The P2 M Ground Theory Heights  Heights Var Branch dim H image le two 99601624bb5f construction uses the P2 M Ground Theory Heights  Heights Var Branch dim H image le two 99601624bb5f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PBranchGermDimOne.lean#L13-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PBranchGermDimOne.lean#L13-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchGermDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZeroSetOpenMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZeroDimIsolated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalDimComponentBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBranchGermDimOne
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
open MvPolynomial ComplexSets Filter Topology
open scoped NNReal ENNReal

theorem P2M_GroundTheory_Heights__Heights_VarBranch_dimH_image_le_two_99601624bb5f {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (c : VarBranch I 1 q) : dimH c.image ≤ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VarBranch».«dimH_image_le_two» := P2M_GroundTheory_Heights__Heights_VarBranch_dimH_image_le_two_99601624bb5f
