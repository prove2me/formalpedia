-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_linProj_zeroExt_b38aab75c095
-- name    : P2M_GroundTheory_Heights__Heights_linProj_zeroExt_b38aab75c095
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:12.210094+00:00
-- url     : https://prove2.me/theorems/ba8041b0-63c0-4c40-a046-71edef808256
-- title:
--   P2 M Ground Theory Heights  Heights lin Proj zero Ext b38aab75c095: P2 M Ground Theory Heights  Heights lin Proj zero Ext b38aab75c095
-- statement:
--   The P2 M Ground Theory Heights  Heights lin Proj zero Ext b38aab75c095 construction uses the P2 M Ground Theory Heights  Heights lin Proj zero Ext b38aab75c095 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMassOfFibre.lean#L108-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMassOfFibre.lean#L108-L111

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibreAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMassOfFibre
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
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_linProj_zeroExt_b38aab75c095 {m k : ℕ} (π : Fin m → Fin (m + k) → ℂ) (x : EuclideanSpace ℂ (Fin m)) :
    linProj π (zeroExt m k x) = WithLp.toLp 2 ((coordPlaneBlock π).mulVec fun i => x i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«linProj_zeroExt» := P2M_GroundTheory_Heights__Heights_linProj_zeroExt_b38aab75c095
