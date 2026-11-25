-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_sum_log_norm_e180af1d2243
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_sum_log_norm_e180af1d2243
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:19:58.323324+00:00
-- url     : https://prove2.me/theorems/3583f8f5-8a79-4568-a1d5-86a026d793a5
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Line Degree Bundle sum log norm e180af1d2243: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Line Deg
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Line Degree Bundle sum log norm e180af1d2243 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Line Degree Bundle sum log norm e180af1d2243 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PLineDegreeBundle.lean#L38-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PLineDegreeBundle.lean#L38-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LineDegreeBundleStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PointHeightDegreeHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PLineDegreeBundle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open NumberField Matrix TensorProduct ComplexAt
open scoped ComplexOrder nonZeroDivisors
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_sum_log_norm_e180af1d2243 {L : Type*} [Field L] [NumberField L] {x : L} (hx : x ≠ 0) :
    ∑ σ : L →+* ℂ, Real.log ‖σ x‖ = Real.log |(Algebra.norm ℚ x : ℝ)| := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«LineDegreeBundle».«sum_log_norm» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_sum_log_norm_e180af1d2243
