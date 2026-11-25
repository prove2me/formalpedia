-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogIntegrableProof_lintegral_lt_top_9a2bece62d68
-- name    : P2M_GroundTheory_Heights__Heights_LogIntegrableProof_lintegral_lt_top_9a2bece62d68
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:28:13.561953+00:00
-- url     : https://prove2.me/theorems/8cc3a710-b9fa-47f6-86c7-6590a46dc79d
-- title:
--   P2 M Ground Theory Heights  Heights Log Integrable Proof lintegral lt top 9a2bece62d68: P2 M Ground Theory Heights  Heights Log Integrable Proof lintegral lt top 9a2bece62d68
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Integrable Proof lintegral lt top 9a2bece62d68 construction uses the P2 M Ground Theory Heights  Heights Log Integrable Proof lintegral lt top 9a2bece62d68 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLogIntegrable.lean#L19-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLogIntegrable.lean#L19-L82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsSheetMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarSlabMeasure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLogIntegrable
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
open MvPolynomial MeasureTheory Set Filter ComplexSets
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LogIntegrableProof
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_LogIntegrableProof_lintegral_lt_top_9a2bece62d68 (hS : VarSlabMeasure.Statement) (hF : MassFinite.Statement) {d : ℕ}
    {J : Ideal (MvPolynomial (Fin n) ℂ)} (u : Fin n → ℂ) (R : ℝ) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) (hu : linForm u ∉ J) :
    ∫⁻ z in zeroSetEuc J ∩ {z | ‖z‖ ≤ R}, ‖Real.log ‖∑ j, u j * z j‖‖ₑ
      ∂(μH[((2 * d : ℕ) : ℝ)]) < ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogIntegrableProof».«lintegral_lt_top» := P2M_GroundTheory_Heights__Heights_LogIntegrableProof_lintegral_lt_top_9a2bece62d68
