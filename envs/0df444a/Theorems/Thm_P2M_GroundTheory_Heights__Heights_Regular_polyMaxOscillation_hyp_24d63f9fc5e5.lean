-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_polyMaxOscillation_hyp_24d63f9fc5e5
-- name    : P2M_GroundTheory_Heights__Heights_Regular_polyMaxOscillation_hyp_24d63f9fc5e5
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:34:54.337703+00:00
-- url     : https://prove2.me/theorems/dc33ee50-1e42-4a45-b71f-bc63bd81555c
-- title:
--   P2 M Ground Theory Heights  Heights Regular poly Max Oscillation hyp 24d63f9fc5e5: P2 M Ground Theory Heights  Heights Regular poly Max Oscillation hyp 24d63f9fc5e5
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular poly Max Oscillation hyp 24d63f9fc5e5 construction uses the P2 M Ground Theory Heights  Heights Regular poly Max Oscillation hyp 24d63f9fc5e5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/Statements.lean#L318-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/Statements.lean#L318-L323

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

theorem P2M_GroundTheory_Heights__Heights_Regular_polyMaxOscillation_hyp_24d63f9fc5e5 (D : ℕ) :
    IsOpen (ball (0 : Fin D → ℂ) 2) ∧ IsPsh (ball (0 : Fin D → ℂ) 2) (fun z => ∑ j, ‖z j‖ ^ 2) ∧
      closedBall (0 : Fin D → ℂ) 1 ⊆ ball 0 2 ∧ (0 : ℝ) < 1 / 4 ∧ (1 : ℝ) ≤ 1 ∧
      (1 : ℝ) * (1 / 4) < 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«polyMaxOscillation_hyp» := P2M_GroundTheory_Heights__Heights_Regular_polyMaxOscillation_hyp_24d63f9fc5e5
