-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartFormsAlt_exists_form_of_mem_chartRing_e51b8144b218
-- name    : P2M_GroundTheory_Heights__Heights_ChartFormsAlt_exists_form_of_mem_chartRing_e51b8144b218
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:18:41.819968+00:00
-- url     : https://prove2.me/theorems/aa7fed50-c946-4234-a19e-b0536423182d
-- title:
--   P2 M Ground Theory Heights  Heights Chart Forms Alt exists form of mem chart Ring e51b8144b218: P2 M Ground Theory Heights  Heights Chart Forms Alt exists form of mem chart Ring e51b8144b218
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Forms Alt exists form of mem chart Ring e51b8144b218 construction uses the P2 M Ground Theory Heights  Heights Chart Forms Alt exists form of mem chart Ring e51b8144b218 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ExistsFormOfMemChartRing.lean#L39-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ExistsFormOfMemChartRing.lean#L39-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ExistsFormOfMemChartRing
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
open GroundTheory.Heights₂.Heights.ChartFormsAlt
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartFormsAlt_exists_form_of_mem_chartRing_e51b8144b218 (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1))
    (hc : P.IsLive c) {x : P.FunField} (hx : x ∈ P.chartRing c) :
    ∃ (F : MvPolynomial (Coord n) ℤ) (e : ι → ℕ), IsWeightedHomogeneous (coordDeg n) F e ∧
      x * P.mkF (chartMonomial c e) = P.mkF F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartFormsAlt».«exists_form_of_mem_chartRing» := P2M_GroundTheory_Heights__Heights_ChartFormsAlt_exists_form_of_mem_chartRing_e51b8144b218
