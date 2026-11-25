-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeSheetArea_proof_67a75eb12888
-- name    : P2M_GroundTheory_Heights__Heights_ConeSheetArea_proof_67a75eb12888
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:04:09.443892+00:00
-- url     : https://prove2.me/theorems/f81f43ac-c3a6-4349-a807-3256495faac8
-- title:
--   P2 M Ground Theory Heights  Heights Cone Sheet Area proof 67a75eb12888: P2 M Ground Theory Heights  Heights Cone Sheet Area proof 67a75eb12888
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Sheet Area proof 67a75eb12888 construction uses the P2 M Ground Theory Heights  Heights Cone Sheet Area proof 67a75eb12888 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetArea.lean#L176-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeSheetArea.lean#L176-L186

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetAreaLintegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeChartArea
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetArea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeChartArea_proof_7d0f995af667
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeIntegralMass_proof_0af09eb068df

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre)
open scoped ENNReal ComplexOrder

theorem P2M_GroundTheory_Heights__Heights_ConeSheetArea_proof_67a75eb12888 (h : ConeSheetAreaLintegral.Statement) : ConeSheetArea.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeSheetArea».«proof» := P2M_GroundTheory_Heights__Heights_ConeSheetArea_proof_67a75eb12888
