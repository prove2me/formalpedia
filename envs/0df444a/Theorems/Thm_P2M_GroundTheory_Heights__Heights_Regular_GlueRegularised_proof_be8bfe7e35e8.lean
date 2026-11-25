-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_GlueRegularised_proof_be8bfe7e35e8
-- name    : P2M_GroundTheory_Heights__Heights_Regular_GlueRegularised_proof_be8bfe7e35e8
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:35:36.045841+00:00
-- url     : https://prove2.me/theorems/f50c2dce-eefa-528c-869e-4ea294f0d834
-- title:
--   P2 M Ground Theory Heights  Heights Regular Glue Regularised proof be8bfe7e35e8: P2 M Ground Theory Heights  Heights Regular Glue Regularised proof be8bfe7e35e8
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Glue Regularised proof be8bfe7e35e8 construction uses the P2 M Ground Theory Heights  Heights Regular Glue Regularised proof be8bfe7e35e8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PGlueRegularised.lean#L87-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PGlueRegularised.lean#L87-L193

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_RegMaxReindex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PGlueRegularised
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
import Theorems.Thm_ReciprocityTheory_AnForm_levi_comp
import Theorems.Thm_ReciprocityTheory_AnForm_levi_congr
import Theorems.Thm_ReciprocityTheory_AnForm_levi_re_analytic

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
open Metric Filter Topology Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh Mollifier molli coordDiv limsupExt regMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_add_smul levi_re_analytic)
noncomputable section
open Classical

theorem P2M_GroundTheory_Heights__Heights_Regular_GlueRegularised_proof_be8bfe7e35e8 : GlueRegularised.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«GlueRegularised».«proof» := P2M_GroundTheory_Heights__Heights_Regular_GlueRegularised_proof_be8bfe7e35e8
