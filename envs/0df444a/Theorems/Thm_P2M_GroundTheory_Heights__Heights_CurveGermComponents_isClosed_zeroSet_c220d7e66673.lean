-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveGermComponents_isClosed_zeroSet_c220d7e66673
-- name    : P2M_GroundTheory_Heights__Heights_CurveGermComponents_isClosed_zeroSet_c220d7e66673
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:36:55.637691+00:00
-- url     : https://prove2.me/theorems/42ae0322-6fb2-4490-aab6-7c6e8836dc1b
-- title:
--   P2 M Ground Theory Heights  Heights Curve Germ Components is Closed zero Set c220d7e66673: P2 M Ground Theory Heights  Heights Curve Germ Components is Closed zero Set c220d7e66673
-- statement:
--   The P2 M Ground Theory Heights  Heights Curve Germ Components is Closed zero Set c220d7e66673 construction uses the P2 M Ground Theory Heights  Heights Curve Germ Components is Closed zero Set c220d7e66673 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCurveGermComponents.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCurveGermComponents.lean#L20-L25

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

theorem P2M_GroundTheory_Heights__Heights_CurveGermComponents_isClosed_zeroSet_c220d7e66673 (J : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSet J) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CurveGermComponents».«isClosed_zeroSet» := P2M_GroundTheory_Heights__Heights_CurveGermComponents_isClosed_zeroSet_c220d7e66673
