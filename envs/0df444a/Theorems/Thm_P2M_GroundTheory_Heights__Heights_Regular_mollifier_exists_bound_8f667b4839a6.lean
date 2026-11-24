-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_mollifier_exists_bound_8f667b4839a6
-- name    : P2M_GroundTheory_Heights__Heights_Regular_mollifier_exists_bound_8f667b4839a6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:32.276949+00:00
-- url     : https://prove2.me/theorems/881fdafb-68c6-461c-bff3-094135c34a1b
-- title:
--   P2 M Ground Theory Heights  Heights Regular mollifier exists bound 8f667b4839a6: P2 M Ground Theory Heights  Heights Regular mollifier exists bound 8f667b4839a6
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular mollifier exists bound 8f667b4839a6 construction uses the P2 M Ground Theory Heights  Heights Regular mollifier exists bound 8f667b4839a6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/Statements.lean#L309-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/Statements.lean#L309-L316

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
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
open MeasureTheory Metric Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh polyMax Mollifier molli coordDiv limsupExt regMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsCompatChart)
open ReciprocityTheory.AnForm (levi)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_mollifier_exists_bound_8f667b4839a6 {D : ℕ} (ρ : Mollifier D) : ∃ b : ℝ, ∀ w, ρ.toFun w ≤ b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«mollifier_exists_bound» := P2M_GroundTheory_Heights__Heights_Regular_mollifier_exists_bound_8f667b4839a6
