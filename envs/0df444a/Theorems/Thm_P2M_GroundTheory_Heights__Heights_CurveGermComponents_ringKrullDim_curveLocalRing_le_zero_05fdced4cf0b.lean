-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveGermComponents_ringKrullDim_curveLocalRing_le_zero_05fdced4cf0b
-- name    : P2M_GroundTheory_Heights__Heights_CurveGermComponents_ringKrullDim_curveLocalRing_le_zero_05fdced4cf0b
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:37:14.779084+00:00
-- url     : https://prove2.me/theorems/6bf0cd13-c88e-47e4-a92f-81ceeda7d597
-- title:
--   P2 M Ground Theory Heights  Heights Curve Germ Components ring Krull Dim curve Local Ring le zero 05fdced4cf0b: P2 M Ground Theory Heights  Heights Curve Germ Components ring Krull Dim curve Local Rin
-- statement:
--   The P2 M Ground Theory Heights  Heights Curve Germ Components ring Krull Dim curve Local Ring le zero 05fdced4cf0b construction uses the P2 M Ground Theory Heights  Heights Curve Germ Components ring Krull Dim curve Local Ring le zero 05fdced4cf0b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCurveGermComponents.lean#L33-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCurveGermComponents.lean#L33-L60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveGermComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalDimDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCurveGermComponents
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
open MvPolynomial ComplexSets Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.CurveGermComponents
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_CurveGermComponents_ringKrullDim_curveLocalRing_le_zero_05fdced4cf0b {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (hm : RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) ∈ I.minimalPrimes) :
    ringKrullDim (curveLocalRing I q) ≤ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CurveGermComponents».«ringKrullDim_curveLocalRing_le_zero» := P2M_GroundTheory_Heights__Heights_CurveGermComponents_ringKrullDim_curveLocalRing_le_zero_05fdced4cf0b
