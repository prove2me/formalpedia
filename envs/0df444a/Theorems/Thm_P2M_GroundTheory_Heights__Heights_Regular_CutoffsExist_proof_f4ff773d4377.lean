-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_CutoffsExist_proof_f4ff773d4377
-- name    : P2M_GroundTheory_Heights__Heights_Regular_CutoffsExist_proof_f4ff773d4377
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:50.575905+00:00
-- url     : https://prove2.me/theorems/9071a65e-4c91-4b5d-ae6b-86e300a15b2b
-- title:
--   P2 M Ground Theory Heights  Heights Regular Cutoffs Exist proof f4ff773d4377: P2 M Ground Theory Heights  Heights Regular Cutoffs Exist proof f4ff773d4377
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Cutoffs Exist proof f4ff773d4377 construction uses the P2 M Ground Theory Heights  Heights Regular Cutoffs Exist proof f4ff773d4377 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PCutoffs.lean#L61-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PCutoffs.lean#L61-L125

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PCutoffs
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_chartPush_eq_zero
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_contDiffOn_compat
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_isCompact_symm_image
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_smooth_chartPush

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Set Filter Topology
open scoped ContDiff Manifold
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm.M.PLAux (chartPush chartPush_eq_zero isCompact_symm_image smooth_chartPush
  contDiffOn_compat)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_CutoffsExist_proof_f4ff773d4377 : CutoffsExist.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«CutoffsExist».«proof» := P2M_GroundTheory_Heights__Heights_Regular_CutoffsExist_proof_f4ff773d4377
