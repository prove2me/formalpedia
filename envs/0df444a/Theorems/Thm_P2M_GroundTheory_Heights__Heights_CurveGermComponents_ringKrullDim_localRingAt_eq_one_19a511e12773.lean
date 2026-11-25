-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveGermComponents_ringKrullDim_localRingAt_eq_one_19a511e12773
-- name    : P2M_GroundTheory_Heights__Heights_CurveGermComponents_ringKrullDim_localRingAt_eq_one_19a511e12773
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:37:27.5642+00:00
-- url     : https://prove2.me/theorems/e5bcba42-2b64-4bf5-9c2d-cf1926a771cc
-- title:
--   P2 M Ground Theory Heights  Heights Curve Germ Components ring Krull Dim local Ring At eq one 19a511e12773: P2 M Ground Theory Heights  Heights Curve Germ Components ring Krull Dim local Ring At eq on
-- statement:
--   The P2 M Ground Theory Heights  Heights Curve Germ Components ring Krull Dim local Ring At eq one 19a511e12773 construction uses the P2 M Ground Theory Heights  Heights Curve Germ Components ring Krull Dim local Ring At eq one 19a511e12773 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCurveGermComponents.lean#L62-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCurveGermComponents.lean#L62-L95

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

theorem P2M_GroundTheory_Heights__Heights_CurveGermComponents_ringKrullDim_localRingAt_eq_one_19a511e12773 {I W : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (hW : W ∈ I.minimalPrimes) (hq : q ∈ zeroSet W) (hdim : ringKrullDim (curveLocalRing I q) = 1) :
    ringKrullDim (localRingAt W q) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CurveGermComponents».«ringKrullDim_localRingAt_eq_one» := P2M_GroundTheory_Heights__Heights_CurveGermComponents_ringKrullDim_localRingAt_eq_one_19a511e12773
