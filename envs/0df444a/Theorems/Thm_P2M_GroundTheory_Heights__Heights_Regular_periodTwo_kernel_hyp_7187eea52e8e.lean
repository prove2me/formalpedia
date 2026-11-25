-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_periodTwo_kernel_hyp_7187eea52e8e
-- name    : P2M_GroundTheory_Heights__Heights_Regular_periodTwo_kernel_hyp_7187eea52e8e
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:34:29.760735+00:00
-- url     : https://prove2.me/theorems/1da6e1f8-5c43-4a15-be34-eb9b8a1a13cd
-- title:
--   P2 M Ground Theory Heights  Heights Regular period Two kernel hyp 7187eea52e8e: P2 M Ground Theory Heights  Heights Regular period Two kernel hyp 7187eea52e8e
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular period Two kernel hyp 7187eea52e8e construction uses the P2 M Ground Theory Heights  Heights Regular period Two kernel hyp 7187eea52e8e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/Statements.lean#L495-L506
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/Statements.lean#L495-L506

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

theorem P2M_GroundTheory_Heights__Heights_Regular_periodTwo_kernel_hyp_7187eea52e8e :
    periodTwo.IsTau0Ext (fun _ => diagonal ![Complex.I, Complex.I]) ∧ (![0, 1] : Fin 2 → ℝ) ≠ 0 ∧
      ∀ i, (periodTwo.B i).map (Int.cast : ℤ → ℝ) *ᵥ ![0, 1] = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«periodTwo_kernel_hyp» := P2M_GroundTheory_Heights__Heights_Regular_periodTwo_kernel_hyp_7187eea52e8e
