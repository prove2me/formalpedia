-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartFormsAlt_chartMonomial_add_31144b20e51b
-- name    : P2M_GroundTheory_Heights__Heights_ChartFormsAlt_chartMonomial_add_31144b20e51b
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:19:42.556622+00:00
-- url     : https://prove2.me/theorems/a7f38744-5103-4dab-b621-6ee803812078
-- title:
--   P2 M Ground Theory Heights  Heights Chart Forms Alt chart Monomial add 31144b20e51b: P2 M Ground Theory Heights  Heights Chart Forms Alt chart Monomial add 31144b20e51b
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Forms Alt chart Monomial add 31144b20e51b construction uses the P2 M Ground Theory Heights  Heights Chart Forms Alt chart Monomial add 31144b20e51b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ExistsFormOfMemChartRing.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ExistsFormOfMemChartRing.lean#L17-L19

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
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_ChartFormsAlt_chartMonomial_add_31144b20e51b (c : (k : ι) → Fin (n k + 1)) (e e' : ι → ℕ) :
    chartMonomial c (e + e') = chartMonomial c e * chartMonomial c e' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartFormsAlt».«chartMonomial_add» := P2M_GroundTheory_Heights__Heights_ChartFormsAlt_chartMonomial_add_31144b20e51b
