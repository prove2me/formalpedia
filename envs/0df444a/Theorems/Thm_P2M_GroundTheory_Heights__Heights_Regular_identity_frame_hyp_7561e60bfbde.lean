-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_identity_frame_hyp_7561e60bfbde
-- name    : P2M_GroundTheory_Heights__Heights_Regular_identity_frame_hyp_7561e60bfbde
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:35:02.246863+00:00
-- url     : https://prove2.me/theorems/ba50348d-0137-58be-8c14-b81d5a7bd768
-- title:
--   P2 M Ground Theory Heights  Heights Regular identity frame hyp 7561e60bfbde: P2 M Ground Theory Heights  Heights Regular identity frame hyp 7561e60bfbde
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular identity frame hyp 7561e60bfbde construction uses the P2 M Ground Theory Heights  Heights Regular identity frame hyp 7561e60bfbde property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/Statements.lean#L508-L511
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/Statements.lean#L508-L511

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

theorem P2M_GroundTheory_Heights__Heights_Regular_identity_frame_hyp_7561e60bfbde (n g : ℕ) :
    (∀ p q, AnalyticOnNhd ℂ (fun _ : Fin n → ℂ => (1 : Matrix (Fin g) (Fin g) ℂ) p q) (ball 0 1)) ∧
      ∀ _z ∈ ball (0 : Fin n → ℂ) 1, (1 : Matrix (Fin g) (Fin g) ℂ).rank = g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«identity_frame_hyp» := P2M_GroundTheory_Heights__Heights_Regular_identity_frame_hyp_7561e60bfbde
