-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_chartX_eq_zero_bb52bd00c10d
-- name    : P2M_GroundTheory_Heights__Heights_ChartKernel_chartX_eq_zero_bb52bd00c10d
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:15:29.289733+00:00
-- url     : https://prove2.me/theorems/eeb5cf7a-7709-42d1-97f1-bb77aae550ea
-- title:
--   P2 M Ground Theory Heights  Heights Chart Kernel chart X eq zero bb52bd00c10d: P2 M Ground Theory Heights  Heights Chart Kernel chart X eq zero bb52bd00c10d
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Kernel chart X eq zero bb52bd00c10d construction uses the P2 M Ground Theory Heights  Heights Chart Kernel chart X eq zero bb52bd00c10d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L180-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L180-L182

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

theorem P2M_GroundTheory_Heights__Heights_ChartKernel_chartX_eq_zero_bb52bd00c10d {g : MvPolynomial (Fin n) F} (hg : g ∈ I ⊔ Ideal.span {linForm t - 1}) :
    chartX I t e g = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartKernel».«chartX_eq_zero» := P2M_GroundTheory_Heights__Heights_ChartKernel_chartX_eq_zero_bb52bd00c10d
