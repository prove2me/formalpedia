-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_proof_1e8f34be57ab
-- name    : P2M_GroundTheory_Heights__Heights_ChartKernel_proof_1e8f34be57ab
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:15:48.598564+00:00
-- url     : https://prove2.me/theorems/b66c6784-d686-4890-bd16-439233c10acd
-- title:
--   P2 M Ground Theory Heights  Heights Chart Kernel proof 1e8f34be57ab: P2 M Ground Theory Heights  Heights Chart Kernel proof 1e8f34be57ab
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Kernel proof 1e8f34be57ab construction uses the P2 M Ground Theory Heights  Heights Chart Kernel proof 1e8f34be57ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L238-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L238-L259

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartKernel
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
open GroundTheory.Heights₂.Heights.ChartKernel
variable {F : Type} [Field F] {n : ℕ}
variable (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ)
variable {I t e}

theorem P2M_GroundTheory_Heights__Heights_ChartKernel_proof_1e8f34be57ab (h₁ : IncidenceGeneric.Statement) (h₂ : ChartIncDomain.Statement) : ChartKernel.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartKernel».«proof» := P2M_GroundTheory_Heights__Heights_ChartKernel_proof_1e8f34be57ab
