-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartFormsAlt_chartMonomial_zero_b41998796e10
-- name    : P2M_GroundTheory_Heights__Heights_ChartFormsAlt_chartMonomial_zero_b41998796e10
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:18:35.663301+00:00
-- url     : https://prove2.me/theorems/6570a1fc-4c63-4f74-a8f7-c75a5fa8a747
-- title:
--   P2 M Ground Theory Heights  Heights Chart Forms Alt chart Monomial zero b41998796e10: P2 M Ground Theory Heights  Heights Chart Forms Alt chart Monomial zero b41998796e10
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Forms Alt chart Monomial zero b41998796e10 construction uses the P2 M Ground Theory Heights  Heights Chart Forms Alt chart Monomial zero b41998796e10 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ExistsFormOfMemChartRing.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ExistsFormOfMemChartRing.lean#L23-L25

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

theorem P2M_GroundTheory_Heights__Heights_ChartFormsAlt_chartMonomial_zero_b41998796e10 (c : (k : ι) → Fin (n k + 1)) :
    chartMonomial c (0 : ι → ℕ) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartFormsAlt».«chartMonomial_zero» := P2M_GroundTheory_Heights__Heights_ChartFormsAlt_chartMonomial_zero_b41998796e10
