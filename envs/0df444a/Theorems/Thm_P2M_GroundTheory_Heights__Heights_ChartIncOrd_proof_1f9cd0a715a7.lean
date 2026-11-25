-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIncOrd_proof_1f9cd0a715a7
-- name    : P2M_GroundTheory_Heights__Heights_ChartIncOrd_proof_1f9cd0a715a7
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:08:03.989171+00:00
-- url     : https://prove2.me/theorems/1831446b-3fd2-50a3-946d-a605e645e382
-- title:
--   P2 M Ground Theory Heights  Heights Chart Inc Ord proof 1f9cd0a715a7: P2 M Ground Theory Heights  Heights Chart Inc Ord proof 1f9cd0a715a7
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Inc Ord proof 1f9cd0a715a7 construction uses the P2 M Ground Theory Heights  Heights Chart Inc Ord proof 1f9cd0a715a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartIncOrd.lean#L190-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartIncOrd.lean#L190-L201

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartIncOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartIncOrd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLocalOrder_proof_c02df12483c9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSection_proof_5b1b05e34c1e

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartIncOrd
variable {F : Type} [Field F] {n : ℕ} (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ)

theorem P2M_GroundTheory_Heights__Heights_ChartIncOrd_proof_1f9cd0a715a7 (h₁ : OrdPolynomialLocalization.Statement) : ChartIncOrd.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIncOrd».«proof» := P2M_GroundTheory_Heights__Heights_ChartIncOrd_proof_1f9cd0a715a7
