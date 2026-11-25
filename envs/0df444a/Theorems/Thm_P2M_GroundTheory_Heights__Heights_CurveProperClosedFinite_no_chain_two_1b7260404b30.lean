-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveProperClosedFinite_no_chain_two_1b7260404b30
-- name    : P2M_GroundTheory_Heights__Heights_CurveProperClosedFinite_no_chain_two_1b7260404b30
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:41.651443+00:00
-- url     : https://prove2.me/theorems/673317f3-f8f4-567a-be28-8bf37c3248d4
-- title:
--   P2 M Ground Theory Heights  Heights Curve Proper Closed Finite no chain two 1b7260404b30: P2 M Ground Theory Heights  Heights Curve Proper Closed Finite no chain two 1b7260404b30
-- statement:
--   The P2 M Ground Theory Heights  Heights Curve Proper Closed Finite no chain two 1b7260404b30 construction uses the P2 M Ground Theory Heights  Heights Curve Proper Closed Finite no chain two 1b7260404b30 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCurveProperClosedFinite.lean#L9-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCurveProperClosedFinite.lean#L9-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveProperClosedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCurveProperClosedFinite
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

theorem P2M_GroundTheory_Heights__Heights_CurveProperClosedFinite_no_chain_two_1b7260404b30 {R : Type*} [CommRing R] {W P Q : Ideal R}
    (hW : W.IsPrime) (hP : P.IsPrime) (hQ : Q.IsPrime) (hdim : ringKrullDim (R ⧸ W) = 1)
    (hWP : W < P) (hPQ : P < Q) : False := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CurveProperClosedFinite».«no_chain_two» := P2M_GroundTheory_Heights__Heights_CurveProperClosedFinite_no_chain_two_1b7260404b30
